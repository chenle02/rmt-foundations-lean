#!/usr/bin/env python3
"""Regenerate inventories and check the Pages site; never invoke Lean or Lake."""
import argparse
import csv
import html
from html.parser import HTMLParser
from pathlib import Path
import re
import shutil
from urllib.parse import unquote, urlsplit

ROOT = Path(__file__).resolve().parent.parent
BASE = 'https://github.com/chenle02/rmt-foundations-lean'
BASE_PATH = '/rmt-foundations-lean/'


class Links(HTMLParser):
    def __init__(self):
        super().__init__()
        self.links = []
        self.ids = set()

    def handle_starttag(self, tag, attrs):
        attrs = dict(attrs)
        if 'id' in attrs:
            if attrs['id'] in self.ids:
                raise ValueError('duplicate anchor: ' + attrs['id'])
            self.ids.add(attrs['id'])
        for key in ('href', 'src'):
            if key in attrs:
                self.links.append(attrs[key])


def module_rows():
    rows = list(csv.DictReader((ROOT / 'MODULES.tsv').open(), delimiter='\t'))
    assert len({r['module'] for r in rows}) == len(rows), 'duplicate modules'
    for r in rows:
        assert (ROOT / r['file']).is_file(), r
        assert r['file'] == r['module'].replace('.', '/') + '.lean', r
    return rows


def claims_rows(modules):
    # The inventory uses unquoted one-line declaration, kind, status and file
    # scalars. Fail closed if this schema changes; summaries are not duplicated.
    text = (ROOT / 'claims.yaml').read_text()
    entries = text.split('\n- id: ')[1:]
    assert entries, 'claims inventory missing'
    rows = []
    for entry in entries:
        row = {}
        for key in ('decl', 'kind', 'status', 'file'):
            values = re.findall(r'^  ' + key + r': ([A-Za-z0-9_./-]+)$', entry, re.M)
            assert len(values) == 1, (key, entry[:100])
            row[key] = values[0]
        assert row['file'] in {m['file'] for m in modules}, row
        rows.append(row)
    assert len({r['decl'] for r in rows}) == len(rows), 'duplicate declarations'
    return rows


def module_table(rows):
    has_api = (ROOT / 'docs/api/RMTFoundations.html').exists()
    return ''.join(
        f'<tr><td><code>{html.escape(r["module"])}</code></td>'
        f'<td><a href="{BASE}/blob/main/{r["file"]}">Source</a></td>'
        + (f'<td><a href="api/{r["file"][:-5]}.html">API</a></td>' if has_api else '')
        + '</tr>' for r in rows)


def declaration_table(rows):
    return ''.join(
        f'<tr id="{html.escape(r["decl"])}"><td><code>{html.escape(r["decl"])}</code></td>'
        f'<td>{html.escape(r["kind"])} / {html.escape(r["status"])}</td>'
        f'<td><a href="{BASE}/blob/main/{r["file"]}">Source statement</a></td></tr>'
        for r in rows)


def update_or_check(path, expected, count, regenerate):
    old = path.read_text()
    new = re.sub(r'<tbody>.*?</tbody>', '<tbody>' + expected + '</tbody>', old, flags=re.S)
    new = re.sub(r': \d+ (registered modules|declarations)', r': ' + str(count) + r' \1', new)
    if regenerate:
        assert not path.is_symlink()
        path.write_text(new)
    else:
        assert old == new, 'regenerate inventory: ' + str(path)


def check_site(root, source=False):
    parsed = {}
    for p in root.rglob('*.html'):
        if '_layouts' in p.relative_to(root).parts:
            continue
        parser = Links()
        parser.feed(p.read_text())
        parsed[p.relative_to(root).as_posix()] = parser
        if 'api' not in p.relative_to(root).parts:
            assert '<html lang="en">' in p.read_text(), p
            assert 'name="viewport"' in p.read_text(), p
        assert 'noindex' not in p.read_text().lower(), 'docs must be indexable: ' + str(p)
    if source:
        for page in root.glob('*.md'):
            text = page.read_text()
            permalink = re.search(r'^permalink: /([^\n]+)$', text, re.M)
            if permalink:
                parser = Links()
                parser.feed(text)
                parser.feed((root / '_layouts/landing.html').read_text())
                parsed[permalink[1]] = parser
    for name, parser in parsed.items():
        if name.startswith('api/'):
            # Generated API dependency links are audited during API extraction.
            continue
        for link in parser.links:
            u = urlsplit(link)
            if u.scheme or u.netloc:
                continue
            rel = unquote(u.path or Path(name).name)
            if rel.startswith('/'):
                assert rel.startswith(BASE_PATH), (name, link)
                target = root / rel[len(BASE_PATH):]
            else:
                target = root / Path(name).parent / rel
            if target.is_dir():
                target = target / 'index.html'
            key = target.relative_to(root).as_posix()
            assert target.exists() or (source and key in parsed), (name, link)
            if u.fragment and target.suffix == '.html':
                assert unquote(u.fragment) in parsed[key].ids, (name, link)
    for name in ('llms.txt', 'CITATION.cff'):
        assert (root / name).read_bytes() == (ROOT / name).read_bytes(), name + ' drift'
    assert not any(p.is_symlink() for p in root.rglob('*'))
    assert not (root / '.nojekyll').exists(), 'use the main:/docs native Jekyll build'
    assert (root / 'assets/mark.svg').is_file()
    assert (root / 'assets/site.css').is_file()
    if not source:
        assert (root / 'index.html').is_file(), 'Jekyll landing missing'
        assert not any(p.name.startswith('_') for p in root.rglob('*')), 'Jekyll internals exported'


def main():
    a = argparse.ArgumentParser(description=__doc__)
    a.add_argument('--check', action='store_true')
    a.add_argument('--regenerate', action='store_true')
    a.add_argument('--site', type=Path, help='Check actual Jekyll output read-only')
    args = a.parse_args()
    assert not any(p.is_symlink() for p in ROOT.rglob('*')
                   if not {'.git', '.lake'} & set(p.relative_to(ROOT).parts))
    modules = module_rows()
    claims = claims_rows(modules)
    update_or_check(ROOT / 'docs/modules.html', module_table(modules), len(modules), args.regenerate)
    update_or_check(ROOT / 'docs/declarations.html', declaration_table(claims), len(claims), args.regenerate)
    if args.regenerate:
        for name in ('llms.txt', 'CITATION.cff'):
            shutil.copy2(ROOT / name, ROOT / 'docs' / name)
    check_site(args.site.absolute() if args.site else ROOT / 'docs', source=not args.site)
    print('DOC_CHECK_PASS', len(modules), 'modules;', len(claims), 'curated declarations;',
          'rendered Jekyll' if args.site else 'main:/docs source')


if __name__ == '__main__':
    main()
