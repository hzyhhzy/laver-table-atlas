"""Bounded independent test of a possible one-sided stretching lemma."""
from array import array
import json
from pathlib import Path
import time

DEGREE = 12
LIMIT_SECONDS = 8.0


def build(degree, deadline):
    size = 1 << degree
    table = [array('H', [0]) * size for _ in range(size)]
    table[0] = array('H', range(size))
    for a in range(size-1, 0, -1):
        if a % 32 == 0 and time.monotonic() > deadline:
            raise TimeoutError('dense A12 build deadline')
        successor = (a+1) % size
        table[a][1] = successor
        for b in range(2, size):
            table[a][b] = table[table[a][b-1]][successor]
    return table


def repeat_bits(value, width):
    out = 0
    while value:
        bit = value & -value
        index = bit.bit_length()-1
        out |= ((1 << width)-1) << (width*index)
        value ^= bit
    return out


def valuation(value):
    return (value & -value).bit_length()-1


def main():
    start = time.monotonic()
    deadline = start+LIMIT_SECONDS
    top = build(DEGREE, deadline)
    records = []
    for width in (2, 4):
        source_degree = DEGREE//width
        bottom = build(source_degree, deadline)
        checks, failures = 0, []
        coordinate_failures = []
        for row in range(1, 1 << source_degree):
            stretched = repeat_bits(row, width)
            source_size = 1 << source_degree
            source_values = {(-value) % source_size for value in bottom[row]}
            for value in set(top[stretched]):
                backward = (-value) % (1 << DEGREE)
                for phase in range(width):
                    coordinate = sum(((backward >> (width*i+phase)) & 1) << i
                                     for i in range(source_degree))
                    if coordinate not in source_values and len(coordinate_failures) < 12:
                        coordinate_failures.append(dict(row=row, target_value=value,
                            backward=backward, phase=phase, coordinate=coordinate,
                            source_backward_subalgebra=sorted(source_values)))
            for argument in range(source_degree):
                source_value = bottom[row][1 << argument]
                source_bound = valuation(source_value) if source_value else source_degree
                target_value = top[stretched][1 << (width*argument)]
                target_bound = valuation(target_value) if target_value else DEGREE
                checks += 1
                if target_value and target_bound < width*source_bound:
                    failures.append(dict(
                        row=row, width=width, argument=argument,
                        stretched_row=stretched, source_degree=source_degree,
                        source_value=source_value, source_image_lower_bound=source_bound,
                        target_value=target_value, target_image=target_bound,
                        claimed_lower_bound=width*source_bound))
        records.append(dict(width=width, checks=checks, failures=failures[:12],
                            failure_count=len(failures),
                            coordinate_failures=coordinate_failures))
    result = dict(
        status='COMPLETED', hypothesis='f_hW(a)(W*r) >= W*f_a(r)',
        scope='A12 only; passing is not a general theorem',
        records=records, seconds=round(time.monotonic()-start, 3),
        raw_cells_bytes=sum(len(row)*row.itemsize for row in top))
    Path(__file__).with_suffix('.json').write_text(json.dumps(result, indent=2)+'\n',
                                                  encoding='utf-8')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()

