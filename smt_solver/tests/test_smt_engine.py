from smt_solver.smt_engine import smt_solver

###### sats ######
s = "~((g(a)=c&(~f(g(a))=f(c)|g(a)=d))&~c=d)"
s1 = "(a=b&(b=c&a=c))" #sat
s2 = "~(f(f(f(a)))=a&(f(f(f(f(f(a)))))=a&~f(a)=a))" #sat
s3 = "(~x=y&f(x)=f(y))" #sat
s4 = "(x=g(y,z)->f(x)=f(g(y,z)))" #valid
s5 = "~(f(a)=a&~f(f(a))=a)" #valid
s6 = "(f(x)=f(y)&~x=y)" #sat
s7 = "~((f(a,c)=b&~f(a,g(b))=b)&c=g(b))"  #sat
###### unsats #######
n = '((g(a)=c&(~f(g(a))=f(c)|g(a)=d))&~c=d)' # unsat
n1 = "(" + s1 + "&~" + s1 + ")" #unsat
n2 = "(f(f(f(a)))=a&(f(f(f(f(f(a)))))=a&~f(a)=a))" #unsat
n3 = "((~x=y&f(x)=f(y))&~(~x=y&f(x)=f(y)))" #unsat
n4 = "~(x=g(y,z)->f(x)=f(g(y,z)))" #unsat
n5 = "(f(a)=a&~f(f(a))=a)" #unsat
n6 = "((f(x)=f(y)&~x=y)&~(f(x)=f(y)&~x=y))" #unsat
n7 = "((f(a,c)=b&~f(a,g(b))=b)&c=g(b))" #unsat

sat_list = [s,s1,s2,s3,s4,s5,s6,s7]
unsat_list = [n,n1,n2,n3,n4, n5,n6,n7]

for s in sat_list:
    assert (smt_solver(s)[0] == 1)

for n in unsat_list:
    if (smt_solver(n)[0] != 0):
        print(n)
        print(smt_solver(n))
    assert (smt_solver(n)[0] == 0)

print("passed!")


# print(smt_solver(n2))