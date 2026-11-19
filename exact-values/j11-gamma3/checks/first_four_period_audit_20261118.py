"""Check the transfer with unequal ranks, aligned-word bounds, and lift guards."""

import json
import time
from pathlib import Path

from interval_minimality_period_probe import build_periods


def audit():
    degree = 16
    deadline = time.monotonic() + 25
    rows, cells = build_periods(degree, deadline)

    def check_clock():
        if time.monotonic() > deadline:
            raise TimeoutError("finite audit exceeded 25 seconds")

    def star(n, a, y):
        value = rows[a][(y - 1) % len(rows[a])] if a else y
        return value % (1 << n)

    def image(a, rank):
        value = star(degree, a, 1 << rank)
        return (value & -value).bit_length() - 1 if value else degree

    def period_exp(n, a):
        return next(r for r in range(n + 1) if not star(n, a, 1 << r))

    transfer = unequal = strictly_ordered = 0
    examples = []
    for n in range(3, 12):
        top = 1 << n
        for left in range(1, min(top, 220)):
            stop = min(18, (1 << period_exp(n, left)) - 2)
            observations = []
            for i in range(1, stop + 1):
                old = star(n, left, i + 1)
                assert old > 1
                actual = star(degree, left, i + 1) - 1
                observations.append([
                    (star(n + 1, old - 1, 1 << r) == top,
                     image(actual, r), image(i, r))
                    for r in range(8)
                ])
            for index, first in enumerate(observations):
                for r, (jump, high, src_high) in enumerate(first):
                    if not jump or high <= n:
                        continue
                    for later, second in enumerate(observations[index + 1:], index + 1):
                        for t, (other_jump, low, src_low) in enumerate(second):
                            if low <= n:
                                continue
                            # At the cutoff equality of two truncated values does
                            # not order them. An exact source comparison also suffices.
                            if not ((low < degree and low <= high) or
                                    (src_low < degree and src_low <= src_high)):
                                continue
                            assert other_jump, (n, left, index + 1, r, later + 1, t)
                            transfer += 1
                            unequal += int(r != t)
                            strictly_ordered += int(low < high or src_low < src_high)
                            if r != t and len(examples) < 4:
                                examples.append([n, left, index + 1, r, later + 1, t])
            check_clock()

    # The hypotheses of Dougherty 6.7 are tested at the exact finite cutoff.
    # Background 0 denotes the identity before taking its ordinary successors.
    guarded = unguarded_failures = 0
    for n in range(5, 15):
        for width in (2, 4, 8):
            for m in range(n // width):
                shift = width * m
                stride = 1 << (shift + width)
                for background in range(0, min(1 << n, 12 * stride), stride):
                    applicable = True
                    for v in range(2, 1 << width):
                        native = background + (v << shift) - 1
                        applicable &= not star(n, native, 1 << width)
                        expected = background + (v << shift)
                        result = star(n, background + (1 << shift) - 1, v)
                        if applicable:
                            assert result == expected
                            guarded += 1
                        elif result != expected:
                            unguarded_failures += 1
        check_clock()

    uniform = []
    for base, m in ((2, 1), (2, 2), (2, 3), (4, 1)):
        width = base ** m
        cutoff = base * width
        exponents = [period_exp(cutoff, x) for x in range(1, (1 << width) - 1)]
        assert max(exponents) <= width
        uniform.append(dict(base=base, m=m, rows=len(exponents), maximum=max(exponents)))

    # D2 4.1 for one aligned replacement, allowing arbitrary higher words.
    restored = 0
    for n in range(5, 14):
        for width in (1, 2, 4, 8):
            for shift in range(0, n - width + 1, width):
                mask = ((1 << width) - 1) << shift
                low = (1 << shift) - 1
                for row in range(low, 1 << n, 1 << shift):
                    filled = row | mask
                    old = period_exp(n, filled)
                    if old > width:
                        continue
                    value = period_exp(n, row)
                    if not (row & mask):
                        assert value == old + width
                    else:
                        assert value <= width
                    restored += 1
        check_clock()
    # Check the two-representation lift as a conditional theorem: the
    # guards are observed on old native composites, never inferred from the
    # desired new products. A background may begin precisely at k*width.
    lifts = backgrounds = touching = extra_bits = 0
    wrong_without_native_guard = 0
    previous_fails = []
    for n in range(5, 16):
        for width in (2, 4):
            for k in range(2, min(width, n // width) + 1):
                cutoff = k * width
                if image((1 << width) - 2, k) != cutoff:
                    continue
                if any(image(v, width) < cutoff for v in range(1, (1 << width) - 1)):
                    continue
                def stretch(i):
                    return sum(((1 << width) - 1) << (width * h)
                               for h in range(k) if i & (1 << h))

                step = 1 << cutoff
                for bg in range(0, min(1 << n, 32 * step), step):
                    left = bg + (1 << width) - 2
                    for i in range(1, (1 << k) - 1):
                        w_row = bg + stretch(i)
                        expected = bg + stretch(i + 1)
                        if star(n, left, i) != w_row or star(n, left, i + 1) != expected:
                            break
                        end = (1 << width) - 1
                        assert star(n, w_row, end) == expected
                        if star(n + 1, expected - 1, 1 << k):
                            if star(n + 1, w_row, left + 1) != expected:
                                wrong_without_native_guard += 1
                                if len(previous_fails) < 3:
                                    previous_fails.append([n, width, k, bg, i])
                            continue
                        assert not star(n + 1, w_row, 1 << cutoff)
                        assert star(n + 1, w_row, end) == expected
                        assert star(n + 1, w_row, left + 1) == expected
                        lifts += 1
                        backgrounds += bool(bg)
                        touching += bool(bg & step)
                        extra_bits += int(bg != 0 and image(left, k) > cutoff)
        check_clock()
    # If the later true image were strictly earlier, that image's bit would
    # be zero, although first-cycle order forced the entire block to be one.
    assert strictly_ordered == 0
    assert unequal and guarded and unguarded_failures and restored
    assert lifts and backgrounds and touching and extra_bits
    half_stable = half_double = 0
    for n in range(3, 13):
        top = 1 << n
        for left in range(1, top):
            p = period_exp(n, left)
            if p < 1:
                continue
            half = 1 << (p - 1)
            last_image = image(left, p - 1)
            assert star(n, left, half) == top - (1 << last_image)
            doubled = period_exp(n + 1, left) > p
            expected = top - (1 << last_image) if doubled else 2 * top - (1 << last_image)
            assert star(n + 1, left, half) == expected
            if doubled:
                for y in range(1, 1 << p):
                    old = star(n, left, y)
                    assert star(n + 1, left, y) == old
                    assert star(n + 1, left, y + (1 << p)) == old + top
                half_double += 1
            else:
                for y in range(half, 1 << p):
                    assert star(n + 1, left, y) == star(n, left, y) + top
                half_stable += 1
        check_clock()

    # Actual exponents only. No array or integer has 2^2048 binary digits.
    base = 256
    exponent_pairs = 0
    for h in range(4, base + 1):
        for m in range(1, h):
            width_exp = 8 * m
            square_block_exp = 8 * (1 << (m.bit_length() - 1))
            assert 8 * (m + 1) <= 2 * square_block_exp
            # The published G2 bound on the source degree is 2^this number.
            license_exp = 2 * (width_exp & -width_exp)
            assert (1 << min(license_exp, 16)) >= base + 1
            if m < h - 1:
                assert base ** (m + 1) < base ** (h - 1) + 1
            else:
                assert base ** (m + 1) == base ** h
            exponent_pairs += 1
        check_clock()
    assert half_stable and half_double
    return dict(max_table_degree=degree, raw_row_payload_bytes=cells * 4,
                transfer_instances=transfer, different_rank_instances=unequal,
                strict_endpoint_order=strictly_ordered, examples_n_row_i_r_j_t=examples,
                valid_six_seven_guards=guarded, failures_without_guards=unguarded_failures,
                aligned_word_restorations=restored, uniform_small_cases=uniform,
                protected_inner_lifts=lifts, nonempty_background_lifts=backgrounds,
                touching_background_lifts=touching, larger_left_image_lifts=extra_bits,
                failures_without_outer_guard=wrong_without_native_guard,
                examples_failing_without_outer_guard=previous_fails,
                unchanged_period_half_rows=half_stable, doubled_period_half_rows=half_double,
                actual_stage_and_width_pairs=exponent_pairs)


if __name__ == "__main__":
    result = audit()
    Path(__file__).with_suffix(".json").write_text(
        json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result))
