# Check D_{-sigma}(Rz) = D_{sigma}(z) - 2 for a random field with the packet reflection
# F(c0 - z) = F(z) - t(z) + k, where t(x) = num*x1 - den*x2, c0 = centre, k = t(c0)/2.
import random
d, n = 5, 3                       # den, num (odd, n < d)
T = d*d + 2*d*n - n*n
L = d + n
c0 = (n + 1, d + 2*n - 1)         # centre = kernel + transverse + (1,-1)
t = lambda x: n*x[0] - d*x[1]
s = lambda x: (d+n)*x[0] + (d-n)*x[1]
assert t(c0) == L - T and s(c0) == T + 2*n, (t(c0), s(c0))
k = t(c0) // 2
assert 2*k == t(c0)
eps, D, N = 1, -2, -1
sigma = (2*eps*D, 2*eps*N)
assert t(sigma) == -2, t(sigma)
random.seed(1)
F = {}
def key(z): return (z[0], z[1])
def val(z):
    if z in F: return F[z]
    w = (c0[0]-z[0], c0[1]-z[1])
    if w == z:
        raise ValueError("fixed point")
    if key(z) < key(w):
        F[z] = random.randint(-50, 50)
    else:
        F[z] = val(w) - t(w) + k      # from F(c0 - w) = F(w) - t(w) + k with w = c0 - z
    return F[z]
def R(z): return (c0[0]-z[0], c0[1]-z[1])
def add(a, b): return (a[0]+b[0], a[1]+b[1])
def sub(a, b): return (a[0]-b[0], a[1]-b[1])
bad = 0; tested = 0
for x in range(-12, 13):
    for y in range(-12, 13):
        z = (x, y)
        if R(z) == z: continue
        try:
            lhs = val(R(z)) - val(sub(R(z), sigma))
            rhs = (val(z) - val(add(z, sigma))) - 2
        except ValueError:
            continue
        tested += 1
        if lhs != rhs: bad += 1
# the reflection itself must be consistent: check F(c0 - z) = F(z) - t(z) + k on the grid
cons = 0
for x in range(-6, 7):
    for y in range(-6, 7):
        z = (x, y)
        if R(z) == z: continue
        try:
            if val(R(z)) != val(z) - t(z) + k: cons += 1
        except ValueError:
            pass
print("tested", tested, "identity failures", bad, "reflection inconsistencies", cons)
