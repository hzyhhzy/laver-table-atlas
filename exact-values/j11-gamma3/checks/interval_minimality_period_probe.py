"""Independent finite probe: is a single interval minimal for later images?

Rows are stored only for one period, using the defining recurrence.
This is bounded evidence, never a proof of a universal comparison theorem.
Memory is capped by a stored-cell bound (80 MiB raw payload) and degree 18.
"""
from array import array
from pathlib import Path
import json
import sys
import time

sys.dont_write_bytecode = True
DEGREE = 18
SECONDS = 22.0
CELL_LIMIT = 20_000_000


def v2(a):
    return (a & -a).bit_length()-1


def build_periods(degree, deadline):
    size = 1 << degree
    rows = [None] * size
    cells = 0
    for a in range(size-1, 0, -1):
        if (a & 127) == 0 and time.monotonic() > deadline:
            raise TimeoutError('table construction deadline')
        step = a+1
        value = step & (size-1)
        row = array('I', [value])
        while value:
            assert value > a
            source = rows[value]
            value = source[(step-1) & (len(source)-1)]
            row.append(value)
        assert len(row) & (len(row)-1) == 0
        cells += len(row)
        if cells > CELL_LIMIT:
            raise MemoryError('stored-cell cap')
        rows[a] = row
    return rows, cells


def main():
    start = time.monotonic()
    records = dict(degree=DEGREE, main_equality='UNRESOLVED',
                   statement='single-block minimality, fixed critical point and first image')
    try:
        rows, cells = build_periods(DEGREE, start+SECONDS)
        def product(a, b, degree=DEGREE):
            if not a:
                return b & ((1 << degree)-1)
            return rows[a][(b-1) & (len(rows[a])-1)] & ((1 << degree)-1)
        # Independent recurrence implementation from the earlier dense test.
        from stretch_growth_probe import build
        small = build(8, start+SECONDS)
        assert all(product(a,b,8) == small[a][b]
                   for a in range(256) for b in range(256))
        # The known small image used in the main paper's low-point input.
        assert v2(product(15, 1 << 8)) == 16
        assert v2(product(240, 1 << 8)) == 16
        failures = []
        checks = 0
        for a in range(1, 1 << DEGREE):
            if (a & 1023) == 0 and time.monotonic() > start+SECONDS:
                raise TimeoutError('comparison deadline')
            critical = v2(a)
            first = critical
            while (a >> first) & 1:
                first += 1
            if first == DEGREE:
                continue
            canonical = (1 << first) - (1 << critical)
            if canonical == a:
                continue
            for argument in range(first, DEGREE):
                canonical_value = product(canonical, 1 << argument)
                canonical_index = v2(canonical_value) if canonical_value else DEGREE
                actual = product(a, 1 << argument)
                actual_index = v2(actual) if actual else DEGREE
                checks += 1
                if actual_index < canonical_index:
                    failures.append(dict(canonical=canonical, row=a,
                        critical=critical, first=first, argument=argument,
                        canonical_image_lower_bound=canonical_index,
                        extension_image_exact=actual_index))
                    if len(failures) == 12:
                        break
            if len(failures) == 12:
                break
        records.update(status='COMPLETED', checks=checks, failures=failures,
                       raw_payload_bytes=4*cells, stored_cells=cells,
                       row_arrays=(1 << DEGREE)-1,
                       scope='finite evidence only; zero is a threshold')
    except (TimeoutError, MemoryError) as exc:
        records.update(status='INCOMPLETE', reason=str(exc))
    records['seconds'] = round(time.monotonic()-start,3)
    Path(__file__).with_suffix('.json').write_text(
        json.dumps(records, indent=2)+'\n', encoding='utf-8')
    print(json.dumps(records, indent=2))


if __name__ == '__main__':
    main()
