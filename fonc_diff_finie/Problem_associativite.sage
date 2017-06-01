my_arctan = DFiniteFunction((y^2+1)*Dy^2 + 2*y*Dy, [0,1])
my_exp = DFiniteFunction(Dy-1, [1])
my_exp_minus = DFiniteFunction(Dy+1, [1])

f=calculate_initial_conditions((my_exp_minus),5)
g=calculate_initial_conditions((my_exp),5)

print (my_exp + my_arctan)*my_exp
print my_exp*my_exp + my_arctan*my_exp