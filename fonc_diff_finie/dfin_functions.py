from ore_algebra import *
from dfin_op import *
from sage.calculus.var import var
from sage.all import *

A = OreAlgebra(QQ['x'], 'Dx')

def complete_coeff(diff_eq):
    """
    This function returns a list with the coefficients of diff_eq
    -diff_eq is a differential of <class 'ore_algebra.ore_operator_1_1.UnivariateDifferentialOperatorOverUnivariateRing'>
    """
    L=[0]*(diff_eq.order()+1)
    mp=copy(diff_eq)
    while(mp!=0):
        coef=mp.coefficients()
        L[mp.order()]=coef[-1]
        ch="Dx^"+str(mp.order())
        d=A(ch)
        mp=mp-L[mp.order()]*d
    return L

def calc_sum_func(L,CI,x):
    """
    -L is a list of functions
    -CI is a list of numbers (Initial conditions at x)
    -x the point at which we evaluate the function
    """
    print L
    if(len(L)!=len(CI)+1):
        raise ValueError,"Incompatible length of L and CI .CI and L must have a length difference of 1"
    t=0
    for i in range(len(L)-1):
        l=L[i](x)
        t+=CI[i]*l
    return -t

def calc_init_con(diff_eq,n):
    """
    Function that calculates the initial condition for Dx^n*f where f is the function that diff_eq describes
    diff_eq is of dfin_op type
    """
    n=int(n)
    if(n<0):
        raise ValueError,"order is always a positive integer"
    length_IC=len(diff_eq.get_init_cond())
    if(length_IC>=n):
        print "IC:",diff_eq.get_init_cond()[:n+1]
        return diff_eq.get_init_cond()[:n+1]
    else:
        d=copy(diff_eq.get_diff_eq())
        Dx=DifferentialOperators()
        d=A('Dx')*d
        L=diff_eq.complete_coeff()
        CI=diff_eq.get_init_cond()
        CI=CI+[calc_sum_func(L,CI,diff_eq.get_x0())]
        order_d=d.order()
        print "Coef:",L
        print "P(x)=",L[0]
        print "P("+str(diff_eq.get_x0())+")=",L[0](diff_eq.get_x0())
        L=complete_coeff(d)
        print "Coef:",L
        print "P(x)=",L[0]
        print "P("+str(diff_eq.get_x0())+")=",L[0](diff_eq.get_x0())
        print "Before add IC:",CI
        CI=CI+[calc_sum_func(L,CI,diff_eq.get_x0())]
        print "After add IC:",CI
        while(n!=order_d):
        
        
        
def complete_init_cond(self,other,op_order):
    """
    This functions calculates the initial conditions using the reccurence series of the differential equation
    """
    self_init_cond_length=len(self.__init_cond)
    other_init_cond_length=len(other.__init_cond)
    if self_init_cond_length == other_init_cond_length :
        i=0
        newlist =[]
        while(i< other_init_cond_length):
            newlist.append(self.__init_cond[i] + other.__init_cond[i])
            i += 1
        l=op_order-len(newlist)
        newlist=newlist+[0]*l
        return newlist

    elif (self_init_cond_length > other_init_cond_length) :
        i = other_init_cond_length - self_init_cond_length
        an=self.get_diff_eq().to_S(OreAlgebra(ZZ["n"], "Sn"))
        an_order=an.order()
        L=[0]*an_order
        j=0
        for k in self.get_init_cond():
            L[j]=k
            j+=1
        order=other.__diff_eq.order()
        L=an.to_list(L,order)
        for j in range(i-1,order):
            L[j]=factorial(j)*L[j]
        i=0
        newlist=[]
        while (i < other_init_cond_length):
            #other.__init_cond.append(...)
            newlist.append(other.__init_cond[i] + L[i])
            i += 1
        l=op_order-len(newlist)
        newlist=newlist+[0]*l
        return newlist
    
    elif (self_init_cond_length < other_init_cond_length) :
        i = other_init_cond_length - self_init_cond_length
        an=self.get_diff_eq().to_S(OreAlgebra(ZZ["n"], "Sn"))
        an_order=an.order()
        L=[0]*an_order
        j=0
        for k in self.get_init_cond():
            L[j]=k
            j+=1
        order=other.__diff_eq.order()
        L=an.to_list(L,order)
        for j in range(i-1,order):
            L[j]=factorial(j)*L[j]
        i=0
        newlist=[]
        while (i < other_init_cond_length):
            #other.__init_cond.append(...)
            newlist.append(other.__init_cond[i] + L[i])
            i += 1
        l=op_order-len(newlist)
        newlist=newlist+[0]*l
        return newlist
    
    
