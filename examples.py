from residue_generator import Rule, Literal, Variable, Constant

w = Variable('w')
x = Variable('x')
y = Variable('y')
z = Variable('z')
u = Variable('u')
v = Variable('v')

print('\nExample 1:')
p1 = Rule(body = [Literal('r', [x, y]), y - x < 1])
p2 = Rule(body = [Literal('r', [u, v]), u > 0, v < 0])
print(f"subsuming clause:\n{p1.show()}")
print(f"subsumed clause:\n{p2.show()}")
print("residues:")
R = p1.partial_subsume(p2)
for r in R:
    print(r.show())
print(f'Total running time: {p1.totalRunTime}s, z3 running time: {p1.z3Time}, z3 is invoked for {p1.z3InvokedTimes} time(s)\n')


print('\nExample 2:')
p1 = Rule(body = [Literal('r', [x, y]), x * y < 1])
p2 = Rule(body = [Literal('r', [u, v]), u > 0, v < 0])
print(f"subsuming clause:\n{p1.show()}")
print(f"subsumed clause:\n{p2.show()}")
print("residues:")
R = p1.partial_subsume(p2)
for r in R:
    print(r.show())
print(f'Total running time: {p1.totalRunTime}s, z3 running time: {p1.z3Time}, z3 is invoked for {p1.z3InvokedTimes} time(s)\n')

print('\nExample 3:')
# example for redundant residues
p1 = Rule(body = [Literal('r1', [w, x]), Literal('r2', [y, z]), y > z])
p2 = Rule(body = [Literal('r1', [u, v]), Literal('r2', [u, v]), u == v])
# by default, a residue is considered redundant if it is always True
# if conditionalRedundant is set to true, then a residue is considered redundant under the condition of the body of the subsumed clause
p1.conditionalRedundant = True
print(f"subsuming clause:\n{p1.show()}")
print(f"subsumed clause:\n{p2.show()}")
print("residues:")
R = p1.partial_subsume(p2)
for r in R:
    print(r.show())
print(f'Total running time: {p1.totalRunTime}s, z3 running time: {p1.z3Time}, z3 is invoked for {p1.z3InvokedTimes} time(s)\n')

print('\nExample 4:')
p1 = Rule(body = [Literal('r', [x, y]), x < y])
p2 = Rule(body = [Literal('r', [u, v]), u > 1, v < -1])
p1.conditionalRedundant = True
print(f"subsuming clause:\n{p1.show()}")
print(f"subsumed clause:\n{p2.show()}")
print("residues:")
R = p1.partial_subsume(p2)
for r in R:
    print(r.show())
print(f'Total running time: {p1.totalRunTime}s, z3 running time: {p1.z3Time}, z3 is invoked for {p1.z3InvokedTimes} time(s)\n')

print('\nExample 5:')
p1 = Rule(body = [Literal('r', [x, y]), x < y])
p2 = Rule(body = [Literal('r', [u, v]), Literal('r', [v, u]), u > 1, v < -1])
p1.conditionalRedundant = True
print(f"subsuming clause:\n{p1.show()}")
print(f"subsumed clause:\n{p2.show()}")
print("residues:")
R = p1.partial_subsume(p2)
for r in R:
    print(r.show())
print(f'Total running time: {p1.totalRunTime}s, z3 running time: {p1.z3Time}, z3 is invoked for {p1.z3InvokedTimes} time(s)\n')

x1 = Variable('x1')
x2 = Variable('x2')
k1 = Constant(1)
k2 = Constant(2)

print('\nExample 6:')
subsumingClause = Rule(body=[Literal('p1', [x2, x2]), Literal('p2', [x2, x1]), Literal('p3', [x1, x2]), Literal('p4', [x2, x1]), Literal('p5', [x2, x1])])
subsumedClause = Rule(body=[Literal('p1', [k1, k2]), Literal('p2', [k1, k2]), Literal('p3', [k1, k1]), Literal('p4', [k1, k2]), Literal('p5', [k1, k1])])
print(f'subsuming clause:\n {subsumingClause.show()}')
print(f'subsumed clause:\n {subsumedClause.show()}')
print("residues:")
residue = subsumingClause.partial_subsume(subsumedClause)
for p in residue:
    print(p.show())
print(f'Total running time: {subsumingClause.totalRunTime}s, z3 running time: {subsumingClause.z3Time}, z3 is invoked for {subsumingClause.z3InvokedTimes} time(s)\n')

print('\nExample 7:')
subsumingClause = Rule(body=[Literal('p1', [x1, x2]), Literal('p1', [x1, x1]), Literal('p3', [x1, x1]), Literal('p3', [x2, x2]), Literal('p5', [x1, x1])])
subsumedClause = Rule(body=[Literal('p1', [k1, k2]), Literal('p1', [k2, k1]), Literal('p3', [k2, k2]), Literal('p4', [k2, k2]), Literal('p5', [k2, k2])])
print(f'subsuming clause:\n {subsumingClause.show()}')
print(f'subsumed clause:\n {subsumedClause.show()}')
print("residues:")
residue = subsumingClause.partial_subsume(subsumedClause)
for p in residue:
    print(p.show())
print(f'Total running time: {subsumingClause.totalRunTime}s, z3 running time: {subsumingClause.z3Time}, z3 is invoked for {subsumingClause.z3InvokedTimes} time(s)\n')
