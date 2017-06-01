print('-------------------------------------------------------------------------')
print("Starting test of calc init")
print("Test of cos4t coef")
print('-------------------------------------------------------------------------')

f=[0]*11
for i in range(11): f[i]=factorial(i)
print f
an=cos4t.annihilator().to_S(OreAlgebra(QQ["n"], "Sn"))
L=an.to_list(cos4t.get_init_cond(),10)
for i in range(1,10): print f[i]*L[i]
print calculate_initial_conditions(cos4t,10)
print('-------------------------------------------------------------------------')

print('Exp3t test of coef')
print('-------------------------------------------------------------------------')

an=exp3t.annihilator().to_S(OreAlgebra(QQ["n"], "Sn"))
L=an.to_list(exp3t.get_init_cond(),10)
for i in range(1,10): print f[i]*L[i]
print calculate_initial_conditions(exp3t,10)
print('-------------------------------------------------------------------------')
