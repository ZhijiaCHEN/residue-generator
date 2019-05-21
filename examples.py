from residue_generator import Rule, Predicate, Variable, Constant

w = Variable('w')
x = Variable('x')
y = Variable('y')
z = Variable('z')
u = Variable('u')
v = Variable('v')

print('\nExample 1:')
p1 = Rule(body = [Predicate('r', [x, y]), y - x < 1])
p2 = Rule(body = [Predicate('r', [u, v]), u > 0, v < 0])
print(f"subsuming clause:\n{p1.show()}")
print(f"subsumed clause:\n{p2.show()}")
print("residues:")
R = p1.partial_subsume(p2)
for r in R:
    print(r.show())
print(f'Total running time: {p1.totalRunTime}s, z3 running time: {p1.z3Time}, z3 is invoked for {p1.z3InvokedTimes} time(s)\n')


print('\nExample 2:')
p1 = Rule(body = [Predicate('r', [x, y]), x * y < 1])
p2 = Rule(body = [Predicate('r', [u, v]), u > 0, v < 0])
print(f"subsuming clause:\n{p1.show()}")
print(f"subsumed clause:\n{p2.show()}")
print("residues:")
R = p1.partial_subsume(p2)
for r in R:
    print(r.show())
print(f'Total running time: {p1.totalRunTime}s, z3 running time: {p1.z3Time}, z3 is invoked for {p1.z3InvokedTimes} time(s)\n')

print('\nExample 3:')
# example for redundant residues
p1 = Rule(body = [Predicate('r1', [w, x]), Predicate('r2', [y, z]), y > z])
p2 = Rule(body = [Predicate('r1', [u, v]), Predicate('r2', [u, v]), u == v])
print(f"subsuming clause:\n{p1.show()}")
print(f"subsumed clause:\n{p2.show()}")
print("residues:")
R = p1.partial_subsume(p2)
for r in R:
    print(r.show())
print(f'Total running time: {p1.totalRunTime}s, z3 running time: {p1.z3Time}, z3 is invoked for {p1.z3InvokedTimes} time(s)\n')

print('\nExample 4:')
p1 = Rule(body = [Predicate('r', [x, y]), x < y])
p2 = Rule(body = [Predicate('r', [u, v]), u > 1, v < -1])
print(f"subsuming clause:\n{p1.show()}")
print(f"subsumed clause:\n{p2.show()}")
print("residues:")
R = p1.partial_subsume(p2)
for r in R:
    print(r.show())
print(f'Total running time: {p1.totalRunTime}s, z3 running time: {p1.z3Time}, z3 is invoked for {p1.z3InvokedTimes} time(s)\n')

print('\nExample 5:')
p1 = Rule(body = [Predicate('r', [x, y]), x < y])
p2 = Rule(body = [Predicate('r', [u, v]), Predicate('r', [v, u]), u > 1, v < -1])
print(f"subsuming clause:\n{p1.show()}")
print(f"subsumed clause:\n{p2.show()}")
print("residues:")
R = p1.partial_subsume(p2)
for r in R:
    print(r.show())
print(f'Total running time: {p1.totalRunTime}s, z3 running time: {p1.z3Time}, z3 is invoked for {p1.z3InvokedTimes} time(s)\n')
