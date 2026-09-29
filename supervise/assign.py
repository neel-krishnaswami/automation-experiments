#!/usr/bin/env python3
"""Assign supervisors to supervision groups, per course, using z3.Optimize.

Reads preferences.csv, writes solved.csv, and prints a report.
See goal.md for the problem statement.
"""

import csv
import sys
from collections import Counter, defaultdict

import z3

# ---------------------------------------------------------------- config

PREFS = 'preferences.csv'
OUT = 'solved.csv'

GROUPS = {'1a': 3, '1b': 4}          # number of supervision groups per year
WEEKS = 8                            # weeks per term
DEFAULT_SUPS = 4                     # 1-hour supervisions per course per group
SUPS_OVERRIDE = {'FHCI': 2, 'Prolog': 3, 'CompNet': 6}
SPLIT_PENALTY = 2                    # rating points lost per extra supervisor on a course
MAX_COURSES_PER_TERM = {'rvb30': 1}   # from their form comment: "1 course/term"
FORBID = set()                       # optional, e.g. {('zl536', '1b-L FHCI')}
TIMEOUT_MS = 60_000                  # per term

TERMS = ['M', 'L', 'E']

# --------------------------------------------------------------- parsing


class Course:
    def __init__(self, header):
        self.id = header                       # e.g. "1a-M Databases"
        self.year = header[:2]                 # "1a" / "1b"
        self.term = header[3]                  # "M" / "L" / "E"
        self.name = header.split(None, 1)[1]
        self.groups = GROUPS[self.year]
        self.hours = SUPS_OVERRIDE.get(self.name, DEFAULT_SUPS)


class Supervisor:
    def __init__(self, row, col):
        self.crsid = row[col['CRSID']].strip()
        self.name = ' '.join(f"{row[col['Given name']]} {row[col['Family name']]}".split())
        self.email = row[col['Email Address']].strip()
        self.min = round(WEEKS * float(row[col['Minimum hours per week desired']] or 0))
        self.max = round(WEEKS * float(row[col['Maximum hours per week desired']] or 0))
        self.rating = {}


def load(path):
    with open(path, newline='') as f:
        rows = list(csv.reader(f))
    header = [h.strip() for h in rows[0]]
    col = {h: i for i, h in enumerate(header)}
    course_cols = defaultdict(list)            # duplicate headers are merged by max
    for i, h in enumerate(header):
        if h.startswith(('1a-', '1b-')):
            course_cols[h].append(i)
    courses = [Course(h) for h in course_cols]
    sups = []
    for row in rows[1:]:
        s = Supervisor(row, col)
        for h, idxs in course_cols.items():
            s.rating[h] = max(int(row[i] or 1) for i in idxs)
        sups.append(s)
    return courses, sups


# ----------------------------------------------------------------- model


def solve_term(courses, sups):
    """Optimal {(crsid, course id): number of groups} for one term's courses.

    Groups of a year are interchangeable, so we only decide how many groups of
    each course a supervisor takes, order-encoded: y[s,c,k] means "s takes at
    least k groups of c".  Objectives are MaxSMT soft constraints; z3 optimises
    soft-constraint ids lexicographically, in the order they are first added.
    """
    y = {(s.crsid, c.id, k): z3.Bool(f'y_{s.crsid}_{c.id}_{k}')
         for s in sups for c in courses for k in range(1, c.groups + 1)}
    opt = z3.Optimize()
    opt.set('timeout', TIMEOUT_MS)

    for c in courses:
        for s in sups:
            for k in range(2, c.groups + 1):
                opt.add(z3.Implies(y[s.crsid, c.id, k], y[s.crsid, c.id, k - 1]))
            if (s.crsid, c.id) in FORBID:
                opt.add(z3.Not(y[s.crsid, c.id, 1]))
        opt.add(z3.PbEq([(y[s.crsid, c.id, k], 1)
                         for s in sups for k in range(1, c.groups + 1)], c.groups))
    load = {s.crsid: [(y[s.crsid, c.id, k], c.hours)
                      for c in courses for k in range(1, c.groups + 1)] for s in sups}
    for s in sups:
        opt.add(z3.PbLe(load[s.crsid], s.max))
        if s.crsid in MAX_COURSES_PER_TERM:
            opt.add(z3.PbLe([(y[s.crsid, c.id, 1], 1) for c in courses],
                            MAX_COURSES_PER_TERM[s.crsid]))

    def penalise(name, weight):
        for s in sups:
            for c in courses:
                for k in range(1, c.groups + 1):
                    w = weight(s.rating[c.id], k)
                    if w:
                        opt.add_soft(z3.Not(y[s.crsid, c.id, k]), w, name)

    # 1. fewest slots rated 1;  2. fewest slots rated <= 2;
    # 3. best total rating, less SPLIT_PENALTY per extra supervisor on a course
    #    (k == 1 is the first group a supervisor takes of a course);
    # 4. fewest hours below supervisors' desired minimums.
    penalise('1-rated-1', lambda r, k: r == 1)
    penalise('2-rated-le-2', lambda r, k: r <= 2)
    penalise('3-preference', lambda r, k: (5 - r) + (SPLIT_PENALTY if k == 1 else 0))
    for s in sups:
        for h in range(1, s.min + 1):
            opt.add_soft(z3.PbGe(load[s.crsid], h), 1, '4-shortfall')

    if opt.check() != z3.sat:
        sys.exit(f'term {courses[0].term}: {opt.check()} ({opt.reason_unknown()})')
    m = opt.model()
    counts = Counter()
    for (crsid, cid, k), v in y.items():
        if z3.is_true(m.eval(v, model_completion=True)):
            counts[crsid, cid] += 1
    return counts


def solve(courses, sups):
    """Capacity is per term, so the terms are independent problems."""
    counts = Counter()
    for t in TERMS:
        in_term = [c for c in courses if c.term == t]
        if in_term:
            counts.update(solve_term(in_term, sups))
    return counts


def expand(courses, counts):
    """Turn per-course counts into [(course, group number, crsid)]."""
    slots, offset = [], Counter()
    for c in courses:
        takers = sorted(((k[0], v) for k, v in counts.items() if k[1] == c.id),
                        key=lambda kv: (-kv[1], kv[0]))
        groups = list(range(1, c.groups + 1))
        if len(takers) > 1:                    # rotate so splits don't always hit group 1
            r = offset[c.year] % c.groups
            groups = groups[r:] + groups[:r]
            offset[c.year] += 1
        it = iter(groups)
        for crsid, k in takers:
            slots += [(c, next(it), crsid) for _ in range(k)]
    return sorted(slots, key=lambda x: (x[0].year, TERMS.index(x[0].term), x[0].id, x[1]))


# ------------------------------------------------------- check and report


def check(courses, all_sups, slots):
    """Independent of z3: validate the expanded allocation."""
    by = {s.crsid: s for s in all_sups}
    seen = Counter((c.id, g) for c, g, _ in slots)
    for c in courses:
        for g in range(1, c.groups + 1):
            assert seen[c.id, g] == 1, f'{c.id} group {g}: {seen[c.id, g]} supervisors'
    assert len(slots) == sum(c.groups for c in courses)
    load = Counter()
    for c, _, crsid in slots:
        load[crsid, c.term] += c.hours
        assert (crsid, c.id) not in FORBID
    for (crsid, t), h in load.items():
        assert h <= by[crsid].max, f'{crsid} over capacity in {t}: {h} > {by[crsid].max}'
    return load


def report(courses, all_sups, sups, slots, load):
    by = {s.crsid: s for s in all_sups}
    ratings = [by[crsid].rating[c.id] for c, _, crsid in slots]
    splits = len({(c.id, crsid) for c, _, crsid in slots}) - len(courses)
    short = sum(max(0, s.min - load[s.crsid, t]) for s in sups for t in TERMS)

    print('Objectives (lexicographic):')
    print(f'  {"slots rated 1":28} {sum(r == 1 for r in ratings)}')
    print(f'  {"slots rated <= 2":28} {sum(r <= 2 for r in ratings)}')
    print(f'  {"extra supervisors on courses":28} {splits}  (penalty {SPLIT_PENALTY} each)')
    print(f'  {"hours below desired minimum":28} {short}')
    best = sum(c.groups * max(s.rating[c.id] for s in sups) for c in courses)
    total = sum(ratings)
    print(f'  {"total rating":28} {total}  (upper bound ignoring capacity: {best})')
    poor = [c.id for c in courses if max(s.rating[c.id] for s in sups) <= 2]
    print(f'  courses nobody rates above 2: {", ".join(poor) or "none"}')

    for year in GROUPS:
        for t in TERMS:
            cs = [c for c in courses if c.year == year and c.term == t]
            if not cs:
                continue
            print(f'\n{year.upper()} {t}' + ''.join(f'{"group " + str(g):>13}'
                                                     for g in range(1, GROUPS[year] + 1)))
            for c in cs:
                cells = {g: crsid for cc, g, crsid in slots if cc is c}
                print(f'  {c.name:12}' + ''.join(
                    f'{cells[g] + "(" + str(by[cells[g]].rating[c.id]) + ")":>13}'
                    for g in sorted(cells)))

    print('\nLoad in h/week (min-max desired):')
    print(f'  {"":8}' + ''.join(f'{t:>7}' for t in TERMS))
    for s in all_sups:
        cells = ''.join(f'{load[s.crsid, t] / WEEKS:7.2f}' for t in TERMS)
        print(f'  {s.crsid:8}{cells}   ({s.min // WEEKS}-{s.max // WEEKS})  {s.name}')
    print('  demand  ' + ''.join(
        f'{sum(c.hours * c.groups for c in courses if c.term == t) / WEEKS:7.2f}'
        for t in TERMS))

    print('\nCourses by supervisor (number of groups, hours in the term):')
    taken = defaultdict(list)                  # (crsid, term, course) -> groups
    for c, g, crsid in slots:
        taken[crsid, c.term, c].append(g)
    for s in sups:
        print(f'  {s.crsid}  {s.name}')
        for t in TERMS:
            items = [(c, gs) for (crsid, term, c), gs in taken.items()
                     if crsid == s.crsid and term == t]
            if not items:
                print(f'    {t}:  -')
            for i, (c, gs) in enumerate(items):
                which = f'{len(gs)} of {c.groups} groups'
                print(f'    {t + ":" if i == 0 else "  "}  {c.year.upper()} {c.name:12}'
                      f'{which:15}{c.hours * len(gs):3}h  (rated {s.rating[c.id]})')

    hist = Counter(by[crsid].rating[c.id] for c, _, crsid in slots)
    print('\nSlots by rating: ' + '  '.join(f'{r}: {hist[r]}' for r in range(5, 0, -1)))
    low = [(c, g, crsid) for c, g, crsid in slots if by[crsid].rating[c.id] <= 2]
    if low:
        print('Slots rated <= 2:')
        for c, g, crsid in low:
            print(f'  {c.id:18} group {g}  {crsid} ({by[crsid].rating[c.id]})')


def write_csv(path, all_sups, slots):
    by = {s.crsid: s for s in all_sups}
    with open(path, 'w', newline='') as f:
        w = csv.writer(f)
        w.writerow(['year', 'term', 'course', 'group', 'crsid', 'name', 'email',
                    'rating', 'hours'])
        for c, g, crsid in slots:
            s = by[crsid]
            w.writerow([c.year.upper(), c.term, c.name, g, crsid, s.name, s.email,
                        s.rating[c.id], c.hours])


def main():
    courses, all_sups = load(PREFS)
    sups = [s for s in all_sups if s.max > 0]
    counts = solve(courses, sups)
    slots = expand(courses, counts)
    load_ = check(courses, all_sups, slots)
    report(courses, all_sups, sups, slots, load_)
    write_csv(OUT, all_sups, slots)
    print(f'\nWrote {OUT}')


if __name__ == '__main__':
    main()
