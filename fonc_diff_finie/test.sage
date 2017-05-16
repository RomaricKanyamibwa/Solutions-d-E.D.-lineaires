print("Starting test script")
from ore_algebra import *;
from  DFiniteFunction import *;R.<y> = PolynomialRing(QQ); A.<Dy> = OreAlgebra(R);K=A.random_element(3);
p=DFiniteFunction(K,[0,1,1],0);
print('-------------------------------------------------------------------------')
K=A.random_element(2);s=DFiniteFunction(K,[0,1],0);
print("Randomly generated functions s and p:")
print('-------------------------------------------------------------------------')
p.print_eq();
s.print_eq();
print('-------------------------------------------------------------------------')
print("Test of __eq__():")
print('-------------------------------------------------------------------------')
l=copy(s)
print "Here we create a copy of s in l"
print "Test if l==s"
print "Result:",l==s
print "Here we test if l==p"
print "Result:",l==p
print('-------------------------------------------------------------------------')
print("Sum of s and p")
print('-------------------------------------------------------------------------')
Z=s+p;
print("s+p")
Z.print_eq()
print('-------------------------------------------------------------------------')
print("Product of s and p")
print('-------------------------------------------------------------------------')
Z=s*p;
print("s*p")
Z.print_eq()
print('-------------------------------------------------------------------------')
print("Test of dfin_function:")
print('-------------------------------------------------------------------------')
#from dfin_functions import *
n=2
calc_init_con(s,n)
calc_init_con(s,n+3)
print('-------------------------------------------------------------------------')
print("Test of dfin_functio:complete list of coefficients")
print('-------------------------------------------------------------------------')
mp=(y^3-5*y)*Dy^5+54*y*Dy^3+0*Dy+y^2-5;L1=[0]*(mp.order()+1)
print "Dif eq:",mp
L=mp.list()
print "Coef:",mp.coefficients()
print "Compl coef:",L
print 'S eq'
print "Dif eq:",s
L=s.coefficients()
print "Coef:",s.get_diff_eq().coefficients()
print "Compl coef:",L

print('-------------------------------------------------------------------------')
print("Test of calc_init_cond on 3*exp(3t)")
print('-------------------------------------------------------------------------')
exp3t=DFiniteFunction(Dy-3,[1])
print "Dif eq:exp3t=",exp3t.get_diff_eq()
n=4
IC=calc_init_con(exp3t,n)
print "Initial condition for n=",n,":",IC
print('-------------------------------------------------------------------------')
print("Sum of exp3t and cos4t")
print('-------------------------------------------------------------------------')
cos4t=DFiniteFunction(Dy^2+16,[1,0])
Z=cos4t+exp3t;
print("cos4t+exp3t")
Z.print_eq()
print('-------------------------------------------------------------------------')
print("Product of exp3t and cos4t")
print('-------------------------------------------------------------------------')
Z=cos4t*exp3t;
print("cos4t*exp3t")
Z.print_eq()
print('-------------------------------------------------------------------------')
print("Dif of exp3t and cos4t")
print('-------------------------------------------------------------------------')
dcos4t=DFiniteFunction(Dy*(Dy^2+16),calc_init_con(cos4t,2))
Z=cos4t-dcos4t;
print("cos4t-cos4t")
Z.print_eq()
print "Test of equality again:"
print "cos4t==dcos4t"
print (cos4t==dcos4t)
print('-------------------------------------------------------------------------')


