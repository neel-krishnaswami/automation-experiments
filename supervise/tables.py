#!/usr/bin/env python3
"""Generate the per-term supervision tables in tex/ from the allocation.

Rows are supervision groups, columns are the supervisors working that term, and
each cell says which courses that supervisor takes that group for, and how many
supervisions of each.  Reads allocation.csv, groups.csv and preferences.csv.
"""

import csv
from collections import defaultdict
from pathlib import Path

# ---------------------------------------------------------------- config

HERE = Path(__file__).parent
ALLOCATION = HERE / 'allocation.csv'
GROUPS = HERE / 'groups.csv'
PREFS = HERE / 'preferences.csv'
OUTDIR = HERE / 'tex'

MICHAELMAS_YEAR = 2026               # Lent and Easter fall in the year after
WEEKS = 8                            # weeks per term
STUDENT_TZ = {'M': 0, 'L': 0, 'E': 1}   # Cambridge's own offset, per term

TERMS = ['M', 'L', 'E']
TERM_NAME = {'M': 'Michaelmas', 'L': 'Lent', 'E': 'Easter'}

PREAMBLE = r"""\documentclass[10pt]{article}
\usepackage[a1paper]{geometry}
\usepackage[T1]{fontenc}
\begin{document}
\thispagestyle{empty}"""

# --------------------------------------------------------------- helpers


def tex(s):
    """Escape the characters that turn up in names and course codes."""
    for a, b in [('\\', r'\textbackslash{}'), ('&', r'\&'), ('%', r'\%'),
                 ('$', r'\$'), ('#', r'\#'), ('_', r'\_'), ('{', r'\{'),
                 ('}', r'\}'), ('~', r'\textasciitilde{}'),
                 ('^', r'\textasciicircum{}')]:
        s = s.replace(a, b)
    return s


def utc(offset):
    return f'UTC{int(offset):+03d}'


def stack(cells):
    r"""A column's worth of per-student lines, as one \newline-joined cell."""
    return r'\newline '.join(cells)


# --------------------------------------------------------------- loading


def load():
    slots = list(csv.DictReader(ALLOCATION.open()))
    students = list(csv.DictReader(GROUPS.open()))

    sups = {}                              # crsid -> {given, family, tz}
    rows = list(csv.DictReader(PREFS.open()))
    tz_col = {t: next(h for h in rows[0]
                      if h.startswith('Your time zone in') and TERM_NAME[t] in h)
              for t in TERMS}
    for r in rows:
        sups[r['CRSID'].strip()] = {
            'given': r['Given name'].strip(),
            'family': r['Family name'].strip(),
            'tz': {t: utc(r[tz_col[t]] or 0) for t in TERMS},
        }
    missing = {s['crsid'] for s in slots} - set(sups)
    if missing:
        raise SystemExit(f'not in {PREFS.name}: {", ".join(sorted(missing))}')
    return slots, students, sups


# ---------------------------------------------------------------- tables


def table(term, slots, students, sups):
    slots = [s for s in slots if s['term'] == term]
    groups = sorted({s['group'] for s in students})
    columns = sorted({s['crsid'] for s in slots},
                     key=lambda c: (sups[c]['family'], sups[c]['given']))

    cell = defaultdict(list)               # (group, crsid) -> ["Course x N"]
    hours = defaultdict(int)               # crsid -> supervisions in the term
    for s in slots:
        n = int(s['supervisions'])
        cell[s['group'], s['crsid']].append(
            f"{tex(s['course'])} $\\times$ {n}")
        hours[s['crsid']] += n

    out = [PREAMBLE,
           r'\begin{tabular}{p{40mm}p{10mm}p{12mm}p{14mm}'
           + '|p{27mm}' * len(columns) + '|}']

    def header(first, cells):
        out.append(first)
        out.extend(f'& {c}' for c in cells)
        out.append(r'\\')

    year = MICHAELMAS_YEAR + (term != 'M')
    header(r'\fbox{\textbf{%s %d}}&&&' % (TERM_NAME[term], year),
           [tex(sups[c]['given']) for c in columns])
    header('&&&', [tex(sups[c]['family']) for c in columns])
    header('&&&', columns)
    header('&&&', [sups[c]['tz'][term] for c in columns])

    for g in groups:
        members = [s for s in students if s['group'] == g]
        out.append(r'\hline')
        out.append(stack(f"{tex(s['given name'])} {tex(s['surname'])}"
                         for s in members))
        for column in (stack(s['crsid'] for s in members),
                       stack(f"CST{s['year'].lower()}" for s in members),
                       stack(utc(STUDENT_TZ[term]) for s in members)):
            out += ['&', column]
        out += [f"& {stack(cell[g, c])}" for c in columns]
        out.append(r'\\')

    out.append(r'\hline')
    out.append('&&&')
    out += [f'& {hours[c]} h; {hours[c] / WEEKS:.1f} h/w' for c in columns]
    out += [r'\\', r'\end{tabular}', r'\end{document}', '']
    return '\n'.join(out)


def main():
    slots, students, sups = load()
    for term in TERMS:
        year = MICHAELMAS_YEAR + (term != 'M')
        path = OUTDIR / f'{year}-{TERM_NAME[term].lower()}-table.tex'
        path.write_text(table(term, slots, students, sups))
        print(f'Wrote {path.relative_to(HERE)}')


if __name__ == '__main__':
    main()
