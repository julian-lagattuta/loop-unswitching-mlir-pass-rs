from z3 import *

# Ok so we have f(t)=2*t^2-t..3x^3-x+1 from 0..100
#  we need that forall 0<= t<100, f(t) < f(t+1)
# we  also need that 
t = Int("t")
solver = Solver()

solver.add(ForAll([t],Implies(And( 0<= t, t < 99), 2*t**2-t <= 2*(t+1)**2-(t+1))))
print(solver.check())
