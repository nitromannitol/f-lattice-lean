"""Scope of the unit increments of the chain potential (task 27): the proper words with child c = d - n < 3, and the
local-input checks (I1, I2, I3a, sheet identity) on the twos family 2^k for k = 1..6, beyond the 116 words.
"""
import open_inputs_check as oc
import permit_local as pl


def main():
    small = []
    for w in pl.proper_words(4):
        fr = oc.frame(w)
        if fr["d"] - fr["n"] < 3:
            small.append((''.join(map(str, w)), fr["eps"]))
    print("proper words of length <= 4 with c = d - n < 3:", small)
    for k in range(1, 7):
        w = tuple([2] * k)
        fr = oc.frame(w)
        r = oc.check_word(w)
        print("2^%d child %d/%d c=%d eps=%d" % (k, fr["n"], fr["d"], fr["d"] - fr["n"], fr["eps"]),
              {x: r[x] for x in ("I1_bad", "I2_bad", "I3_bad", "id_bad")})


if __name__ == "__main__":
    main()
