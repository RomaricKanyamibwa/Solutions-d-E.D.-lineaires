from ore_algebra import *
from dfin_op import *
from sage.calculus.var import var
from sage.all import *



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
        A = OreAlgebra(QQ['x'], 'Dx')
        d=A('Dx')*d
        L=diff_eq.get_diff_eq().coefficients()
        print "Coef:",L
        print "P(x)=",L[0]
        print "P(1)=",L[0](1)
        L=d.coefficients()
        print "Coef:",L
        print "P(x)=",L[0]
        print "P(1)=",L[0](1)
        L=L+[]
        
        
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
    
    