from math import sqrt

# Funciones auxiliares para nussinov
def __max_score(s1, s2):
    if s1 >= s2:
        return s1
    return s2


def __match(b1, b2):
    if b1 + b2 == 3:
        return 1
    return 0



def scop_covariance(_PB_M,_PB_N,cov,mean,data,float_n):
    if((_PB_M-1>= 0)):
        if((_PB_N*-1>= 0)):
            for c1 in range (_PB_M):
                for c2 in range (c1 , _PB_M):
                    (cov[c1])[c2]=0.0
                    (cov[c1])[c2]=(((cov[c1])[c2])/(float_n+(-1*1.0)))
                    (cov[c2])[c1]=((cov[c1])[c2])
        if((_PB_N-1>= 0)):
            for c1 in range (_PB_M):
                for c2 in range (c1 , _PB_M):
                    (cov[c1])[c2]=0.0
        if((_PB_N*-1>= 0)):
            for c1 in range (_PB_M):
                mean[c1]=0.0
                mean[c1]=((mean[c1])/float_n)
        if((_PB_N-1>= 0)):
            for c1 in range (_PB_M):
                mean[c1]=0.0
        if((_PB_N-1>= 0)):
            for c1 in range (_PB_M):
                for c2 in range (_PB_N):
                    mean[c1]=((mean[c1])+((data[c2])[c1]))
        if((_PB_N-1>= 0)):
            for c1 in range (_PB_M):
                mean[c1]=((mean[c1])/float_n)
        for c1 in range (_PB_N):
            for c2 in range (_PB_M):
                (data[c1])[c2]=(((data[c1])[c2])+(-1*(mean[c2])))
        if((_PB_N-1>= 0)):
            for c1 in range (_PB_M):
                for c2 in range (c1 , _PB_M):
                    for c3 in range (_PB_N):
                        (cov[c1])[c2]=(((cov[c1])[c2])+(((data[c3])[c1])*((data[c3])[c2])))
        if((_PB_N-1>= 0)):
            for c1 in range (_PB_M):
                for c2 in range (c1 , _PB_M):
                    (cov[c1])[c2]=(((cov[c1])[c2])/(float_n+(-1*1.0)))
                    (cov[c2])[c1]=((cov[c1])[c2])
    return (_PB_M,_PB_N,cov,mean,data,float_n)


def scop_gemm(_PB_NI,_PB_NJ,_PB_NK,alpha,beta,A,B,C):
    if((_PB_NI-1>= 0) and (_PB_NJ-1>= 0)):
        for c1 in range (_PB_NI):
            for c2 in range (_PB_NJ):
                (C[c1])[c2]=(((C[c1])[c2])*beta)
        if((_PB_NK-1>= 0)):
            for c1 in range (_PB_NI):
                for c2 in range (_PB_NJ):
                    for c3 in range (_PB_NK):
                        (C[c1])[c2]=(((C[c1])[c2])+((alpha*((A[c1])[c3]))*((B[c3])[c2])))
    return (_PB_NI,_PB_NJ,_PB_NK,alpha,beta,A,B,C)


def scop_gemver(_PB_N,alpha,beta,A,u1,u2,v1,v2,w,x,y,z):
    if((_PB_N-1>= 0)):
        for c1 in range (_PB_N):
            for c2 in range (_PB_N):
                (A[c2])[c1]=((((A[c2])[c1])+((u1[c2])*(v1[c1])))+((u2[c2])*(v2[c1])))
                x[c1]=((x[c1])+((beta*((A[c2])[c1]))*(y[c2])))
        for c1 in range (_PB_N):
            x[c1]=((x[c1])+(z[c1]))
        for c1 in range (_PB_N):
            for c2 in range (_PB_N):
                w[c1]=((w[c1])+((alpha*((A[c1])[c2]))*(x[c2])))
    return (_PB_N,alpha,beta,A,u1,u2,v1,v2,w,x,y,z)


def scop_gesummv(_PB_N,alpha,beta,A,B,tmp,x,y):
    if((_PB_N-1>= 0)):
        for c1 in range (_PB_N):
            y[c1]=0.0
        for c1 in range (_PB_N):
            for c2 in range (_PB_N):
                y[c1]=((((B[c1])[c2])*(x[c2]))+(y[c1]))
        for c1 in range (_PB_N):
            tmp[c1]=0.0
        for c1 in range (_PB_N):
            for c2 in range (_PB_N):
                tmp[c1]=((((A[c1])[c2])*(x[c2]))+(tmp[c1]))
        for c1 in range (_PB_N):
            y[c1]=((alpha*(tmp[c1]))+(beta*(y[c1])))
    return (_PB_N,alpha,beta,A,B,tmp,x,y)


def scop_symm(_PB_N,_PB_M,alpha,beta,A,B,C):
    if((_PB_M-1>= 0) and (_PB_N-1>= 0)):
        for c2 in range (_PB_N):
            temp2=0
            (C[0])[c2]=(((beta*((C[0])[c2]))+((alpha*((B[0])[c2]))*((A[0])[0])))+(alpha*temp2))
        for c1 in range (1 , _PB_M):
            for c2 in range (_PB_N):
                (C[0])[c2]=(((C[0])[c2])+((alpha*((B[c1])[c2]))*((A[c1])[0])))
                temp2=0
                temp2=(temp2+(((B[0])[c2])*((A[c1])[0])))
                for c3 in range (1 , c1):
                    (C[c3])[c2]=(((C[c3])[c2])+((alpha*((B[c1])[c2]))*((A[c1])[c3])))
                    temp2=(temp2+(((B[c3])[c2])*((A[c1])[c3])))
                (C[c1])[c2]=(((beta*((C[c1])[c2]))+((alpha*((B[c1])[c2]))*((A[c1])[c1])))+(alpha*temp2))
    return (_PB_N,_PB_M,alpha,beta,A,B,C)


def scop_syr2k(_PB_N,_PB_M,alpha,beta,A,B,C):
    if((_PB_N-1>= 0)):
        for c1 in range (_PB_N):
            for c2 in range (c1 + 1):
                (C[c1])[c2]=(((C[c1])[c2])*beta)
        if((_PB_M-1>= 0)):
            for c1 in range (_PB_N):
                for c2 in range (c1 + 1):
                    for c3 in range (_PB_M):
                        (C[c1])[c2]=(((C[c1])[c2])+(((((A[c2])[c3])*alpha)*((B[c1])[c3]))+((((B[c2])[c3])*alpha)*((A[c1])[c3]))))
    return (_PB_N,_PB_M,alpha,beta,A,B,C)


def scop_syrk(_PB_N,_PB_M,alpha,beta,A,C):
    if((_PB_N-1>= 0)):
        for c1 in range (_PB_N):
            for c2 in range (c1 + 1):
                (C[c1])[c2]=(((C[c1])[c2])*beta)
        if((_PB_M-1>= 0)):
            for c1 in range (_PB_N):
                for c2 in range (c1 + 1):
                    for c3 in range (_PB_M):
                        (C[c1])[c2]=(((C[c1])[c2])+((alpha*((A[c1])[c3]))*((A[c2])[c3])))
    return (_PB_N,_PB_M,alpha,beta,A,C)


def scop_trmm(_PB_N,_PB_M,alpha,A,B):
    if((_PB_M-1>= 0) and (_PB_N-1>= 0)):
        if((_PB_M-2>= 0)):
            for c1 in range (_PB_N):
                for c2 in range (_PB_M-1):
                    for c3 in range (c2 + 1 , _PB_M):
                        (B[c2])[c1]=(((B[c2])[c1])+(((A[c3])[c2])*((B[c3])[c1])))
        for c1 in range (_PB_M):
            for c2 in range (_PB_N):
                (B[c1])[c2]=(alpha*((B[c1])[c2]))
    return (_PB_N,_PB_M,alpha,A,B)


def scop_2mm(_PB_NI,_PB_NJ,_PB_NK,_PB_NL,tmp,alpha,beta,A,B,C,D):
    if((_PB_NI-1>= 0)):
        if((_PB_NJ-1>= 0) and (_PB_NL-1>= 0)):
            for c1 in range (_PB_NI):
                for c2 in range (min(_PB_NJ , _PB_NL)):
                    (D[c1])[c2]=(((D[c1])[c2])*beta)
                    (tmp[c1])[c2]=0.0
                for c2 in range (_PB_NL , _PB_NJ):
                    (tmp[c1])[c2]=0.0
                for c2 in range (_PB_NJ , _PB_NL):
                    (D[c1])[c2]=(((D[c1])[c2])*beta)
        if((_PB_NJ-1>= 0) and (_PB_NL*-1>= 0)):
            for c1 in range (_PB_NI):
                for c2 in range (_PB_NJ):
                    (tmp[c1])[c2]=0.0
        if((_PB_NJ*-1>= 0) and (_PB_NL-1>= 0)):
            for c1 in range (_PB_NI):
                for c2 in range (_PB_NL):
                    (D[c1])[c2]=(((D[c1])[c2])*beta)
        if((_PB_NJ-1>= 0) and (_PB_NK-1>= 0) and (_PB_NL-1>= 0)):
            for c1 in range (_PB_NI):
                for c2 in range (_PB_NJ):
                    for c5 in range (_PB_NK):
                        (tmp[c1])[c2]=(((tmp[c1])[c2])+((alpha*((A[c1])[c5]))*((B[c5])[c2])))
                    for c5 in range (_PB_NL):
                        (D[c1])[c5]=(((D[c1])[c5])+(((tmp[c1])[c2])*((C[c2])[c5])))
        if((_PB_NJ-1>= 0) and (_PB_NK-1>= 0) and (_PB_NL*-1>= 0)):
            for c1 in range (_PB_NI):
                for c2 in range (_PB_NJ):
                    for c5 in range (_PB_NK):
                        (tmp[c1])[c2]=(((tmp[c1])[c2])+((alpha*((A[c1])[c5]))*((B[c5])[c2])))
        if((_PB_NJ-1>= 0) and (_PB_NK*-1>= 0) and (_PB_NL-1>= 0)):
            for c1 in range (_PB_NI):
                for c2 in range (_PB_NJ):
                    for c5 in range (_PB_NL):
                        (D[c1])[c5]=(((D[c1])[c5])+(((tmp[c1])[c2])*((C[c2])[c5])))
    return (_PB_NI,_PB_NJ,_PB_NK,_PB_NL,tmp,alpha,beta,A,B,C,D)


def scop_3mm(_PB_NI,_PB_NJ,_PB_NK,_PB_NL,_PB_NM,A,B,C,D,E,F,G):
    if((_PB_NL-1>= 0)):
        for c1 in range (min(_PB_NI , _PB_NJ)):
            for c2 in range (_PB_NL):
                (G[c1])[c2]=0.0
                (F[c1])[c2]=0.0
    if((_PB_NL-1>= 0)):
        for c1 in range (max(0 , _PB_NI) , _PB_NJ):
            for c2 in range (_PB_NL):
                (F[c1])[c2]=0.0
    if((_PB_NL-1>= 0)):
        for c1 in range (max(0 , _PB_NJ) , _PB_NI):
            for c2 in range (_PB_NL):
                (G[c1])[c2]=0.0
    if((_PB_NL-1>= 0) and (_PB_NM-1>= 0)):
        for c1 in range (_PB_NJ):
            for c2 in range (_PB_NL):
                for c5 in range (_PB_NM):
                    (F[c1])[c2]=(((F[c1])[c2])+(((C[c1])[c5])*((D[c5])[c2])))
    if((_PB_NJ-1>= 0)):
        for c1 in range (_PB_NI):
            for c2 in range (_PB_NJ):
                (E[c1])[c2]=0.0
    if((_PB_NJ-1>= 0) and (_PB_NK-1>= 0) and (_PB_NL-1>= 0)):
        for c1 in range (_PB_NI):
            for c2 in range (_PB_NJ):
                for c5 in range (_PB_NK):
                    (E[c1])[c2]=(((E[c1])[c2])+(((A[c1])[c5])*((B[c5])[c2])))
                for c5 in range (_PB_NL):
                    (G[c1])[c5]=(((G[c1])[c5])+(((E[c1])[c2])*((F[c2])[c5])))
    if((_PB_NJ-1>= 0) and (_PB_NK-1>= 0) and (_PB_NL*-1>= 0)):
        for c1 in range (_PB_NI):
            for c2 in range (_PB_NJ):
                for c5 in range (_PB_NK):
                    (E[c1])[c2]=(((E[c1])[c2])+(((A[c1])[c5])*((B[c5])[c2])))
    if((_PB_NJ-1>= 0) and (_PB_NK*-1>= 0) and (_PB_NL-1>= 0)):
        for c1 in range (_PB_NI):
            for c2 in range (_PB_NJ):
                for c5 in range (_PB_NL):
                    (G[c1])[c5]=(((G[c1])[c5])+(((E[c1])[c2])*((F[c2])[c5])))
    return (_PB_NI,_PB_NJ,_PB_NK,_PB_NL,_PB_NM,A,B,C,D,E,F,G)



def scop_atax(_PB_N,_PB_M,A,x,y,tmp):
    for c1 in range (_PB_M):
        tmp[c1]=0.0
    if((_PB_N-1>= 0)):
        for c1 in range (_PB_M):
            for c2 in range (_PB_N):
                tmp[c1]=((tmp[c1])+(((A[c1])[c2])*(x[c2])))
    for c1 in range (_PB_N):
        y[c1]=0
    if((_PB_M-1>= 0)):
        for c1 in range (_PB_N):
            for c2 in range (_PB_M):
                y[c1]=((y[c1])+(((A[c2])[c1])*(tmp[c2])))
    return (_PB_N,_PB_M,A,x,y,tmp)



def scop_bicg(_PB_N,_PB_M,A,p,q,r,s):
    for c1 in range (_PB_N):
        q[c1]=0.0
    if((_PB_M-1>= 0)):
        for c1 in range (_PB_N):
            for c2 in range (_PB_M):
                q[c1]=((q[c1])+(((A[c1])[c2])*(p[c2])))
    for c1 in range (_PB_M):
        s[c1]=0
    if((_PB_N-1>= 0)):
        for c1 in range (_PB_M):
            for c2 in range (_PB_N):
                s[c1]=((s[c1])+((r[c2])*((A[c2])[c1])))
    return (_PB_N,_PB_M,A,p,q,r,s)


def scop_doitgen(_PB_NR,_PB_NQ,_PB_NP,A,C4,suma):
    if((_PB_NP-1>= 0) and (_PB_NQ-1>= 0) and (_PB_NR-1>= 0)):
        for c0 in range (_PB_NR):
            for c1 in range (_PB_NQ):
                for c3 in range (_PB_NP):
                    suma[c3]=0.0
                for c3 in range (_PB_NP):
                    for c4 in range (_PB_NP):
                        suma[c3]=((suma[c3])+((((A[c0])[c1])[c4])*((C4[c4])[c3])))
                for c3 in range (_PB_NP):
                    ((A[c0])[c1])[c3]=(suma[c3])
    return (_PB_NR,_PB_NQ,_PB_NP,A,C4,suma)


def scop_mvt(_PB_N,A,x1,x2,y_1,y_2):
    if((_PB_N-1>= 0)):
        for c1 in range (_PB_N):
            for c2 in range (_PB_N):
                x1[c1]=((x1[c1])+(((A[c1])[c2])*(y_1[c2])))
                x2[c1]=((x2[c1])+(((A[c2])[c1])*(y_2[c2])))
    return (_PB_N,A,x1,x2,y_1,y_2)


def scop_cholesky(_PB_N,A,p):
    if((_PB_N-1>= 0)):
        (A[0])[0]=sqrt(((A[0])[0]))
        if((_PB_N-2>= 0)):
            (A[1])[0]=(((A[1])[0])/((A[0])[0]))
        if((_PB_N-2>= 0)):
            (A[1])[1]=(((A[1])[1])+(-1*(((A[1])[0])*((A[1])[0]))))
        if((_PB_N-2>= 0)):
            (A[1])[1]=sqrt(((A[1])[1]))
        for c0 in range (2 , _PB_N):
            (A[c0])[0]=(((A[c0])[0])/((A[0])[0]))
            (A[c0])[c0]=(((A[c0])[c0])+(-1*(((A[c0])[0])*((A[c0])[0]))))
            for c1 in range (1 , c0):
                for c2 in range (c1):
                    (A[c0])[c1]=(((A[c0])[c1])+(-1*(((A[c0])[c2])*((A[c1])[c2]))))
                (A[c0])[c1]=(((A[c0])[c1])/((A[c1])[c1]))
                (A[c0])[c0]=(((A[c0])[c0])+(-1*(((A[c0])[c1])*((A[c0])[c1]))))
            (A[c0])[c0]=sqrt(((A[c0])[c0]))
    return (_PB_N,A,p)



def scop_durbin(_PB_N,alpha,beta,suma,y,r,z):
    if((_PB_N-2>= 0)):
        for c0 in range (1 , _PB_N):
            suma=0.0
            suma=(suma+((r[((c0+(-1*0))+(-1*1))])*(y[0])))
            beta=((1+(-1*(alpha*alpha)))*beta)
            for c1 in range (1 , c0):
                suma=(suma+((r[((c0+(-1*c1))+(-1*1))])*(y[c1])))
            alpha=((-1*((r[c0])+suma))/beta)
            y[c0]=alpha
            for c1 in range (c0 , c0 * 2):
                z[(-1 * c0) + c1]=((y[(-1 * c0) + c1])+(alpha*(y[((c0+(-1*(-1 * c0) + c1))+(-1*1))])))
            for c1 in range (c0 * 2 , c0 * 3):
                y[(-2 * c0) + c1]=(z[(-2 * c0) + c1])
    return (_PB_N,alpha,beta,suma,y,r,z)

def scop_gramschmidt(_PB_N,_PB_M,A,Q,R):
    if((_PB_N-1>= 0)):
        for c1 in range (_PB_N-1):
            for c3 in range (c1 + 1 , _PB_N):
                (R[c1])[c3]=0.0
        if((_PB_M-1>= 0)):
            for c1 in range (_PB_N-1):
                nrm=0.0
                for c3 in range (_PB_M):
                    nrm=(nrm+(((A[c3])[c1])*((A[c3])[c1])))
                (R[c1])[c1]=sqrt(nrm)
                for c3 in range (_PB_M):
                    (Q[c3])[c1]=(((A[c3])[c1])/((R[c1])[c1]))
                for c3 in range (c1 + 1 , _PB_N):
                    for c6 in range (_PB_M):
                        (R[c1])[c3]=(((R[c1])[c3])+(((Q[c6])[c1])*((A[c6])[c3])))
                    for c6 in range (_PB_M):
                        (A[c6])[c3]=(((A[c6])[c3])+(-1*(((Q[c6])[c1])*((R[c1])[c3]))))
        if((_PB_M-1>= 0)):
            nrm=0.0
        if((_PB_M-1>= 0)):
            for c3 in range (_PB_M):
                nrm=(nrm+(((A[c3])[_PB_N + -1])*((A[c3])[_PB_N + -1])))
        if((_PB_M-1>= 0)):
            (R[_PB_N + -1])[_PB_N + -1]=sqrt(nrm)
        if((_PB_M-1>= 0)):
            for c3 in range (_PB_M):
                (Q[c3])[_PB_N + -1]=(((A[c3])[_PB_N + -1])/((R[_PB_N + -1])[_PB_N + -1]))
        if((_PB_M*-1>= 0)):
            for c1 in range (_PB_N):
                nrm=0.0
                (R[c1])[c1]=sqrt(nrm)
    return (_PB_N,_PB_M,A,Q,R)


def scop_lu(_PB_N,A):
    if((_PB_N-2>= 0)):
        (A[1])[0]=(((A[1])[0])/((A[0])[0]))
        for c1 in range (1 , _PB_N):
            (A[1])[c1]=(((A[1])[c1])+(-1*(((A[1])[0])*((A[0])[c1]))))
        for c0 in range (2 , _PB_N):
            (A[c0])[0]=(((A[c0])[0])/((A[0])[0]))
            for c1 in range (1 , c0):
                for c2 in range (c1):
                    (A[c0])[c1]=(((A[c0])[c1])+(-1*(((A[c0])[c2])*((A[c2])[c1]))))
                (A[c0])[c1]=(((A[c0])[c1])/((A[c1])[c1]))
            for c1 in range (c0 , _PB_N):
                for c2 in range (c0):
                    (A[c0])[c1]=(((A[c0])[c1])+(-1*(((A[c0])[c2])*((A[c2])[c1]))))
    return (_PB_N,A)


def scop_ludcmp(_PB_N,A,b,x,y):
    if((_PB_N-1>= 0)):
        for c5 in range (_PB_N):
            w=((A[0])[c5])
            (A[0])[c5]=w
        if((_PB_N-2>= 0)):
            w=((A[1])[0])
        if((_PB_N-2>= 0)):
            (A[1])[0]=(w/((A[0])[0]))
        if((_PB_N-2>= 0)):
            for c5 in range (1 , _PB_N):
                w=((A[1])[c5])
                w=(w+(-1*(((A[1])[0])*((A[0])[c5]))))
                (A[1])[c5]=w
        for c3 in range (2 , _PB_N):
            w=((A[c3])[0])
            (A[c3])[0]=(w/((A[0])[0]))
            for c5 in range (1 , c3):
                w=((A[c3])[c5])
                for c6 in range (c5):
                    w=(w+(-1*(((A[c3])[c6])*((A[c6])[c5]))))
                (A[c3])[c5]=(w/((A[c5])[c5]))
            for c5 in range (c3 , _PB_N):
                w=((A[c3])[c5])
                for c6 in range (c3):
                    w=(w+(-1*(((A[c3])[c6])*((A[c6])[c5]))))
                (A[c3])[c5]=w
        w=(b[0])
        y[0]=w
        for c3 in range (1 , _PB_N):
            w=(b[c3])
            for c5 in range (c3):
                w=(w+(-1*(((A[c3])[c5])*(y[c5]))))
            y[c3]=w
        for c3 in range (min(2 , _PB_N)):
            w=(y[(_PB_N+(-1*1))])
            x[((_PB_N+(-1*c3))+(-1*1))]=(w/((A[((_PB_N+(-1*c3))+(-1*1))])[((_PB_N+(-1*c3))+(-1*1))]))
        for c3 in range (2 , _PB_N):
            w=(y[(_PB_N+(-1*1))])
            for c5 in range (_PB_N + c3 * -1 + 1 , _PB_N):
                w=(w+(-1*(((A[(_PB_N+(-1*c3))])[c5])*(x[c5]))))
            x[((_PB_N+(-1*c3))+(-1*1))]=(w/((A[((_PB_N+(-1*c3))+(-1*1))])[((_PB_N+(-1*c3))+(-1*1))]))
    return (_PB_N,A,b,x,y)


def scop_trisolv(_PB_N,L,x,b):
    if((_PB_N-1>= 0)):
        for c1 in range (_PB_N):
            x[c1]=(b[c1])
        x[0]=((x[0])/((L[0])[0]))
        for c1 in range (1 , _PB_N):
            for c2 in range (c1):
                x[c1]=((x[c1])+(-1*(((L[c1])[c2])*(x[c2]))))
            x[c1]=((x[c1])/((L[c1])[c1]))
    return (_PB_N,L,x,b)


def scop_deriche(_PB_W,_PB_H,a1,a2,a3,a4,a5,a6,a7,a8,b1,b2,c1,c2,y1,y2,imgIn,imgOut):
    if((_PB_H-1>= 0)):
        for c3 in range (_PB_W):
            yp1=0.0
            yp2=0.0
            xp1=0.0
            xp2=0.0
            for c5 in range (_PB_H):
                (y2[c3])[((_PB_H+(-1*1))+(-1*c5))]=((((a3*xp1)+(a4*xp2))+(b1*yp1))+(b2*yp2))
                yp2=yp1
                yp1=((y2[c3])[((_PB_H+(-1*1))+(-1*c5))])
                xp2=xp1
                xp1=((imgIn[c3])[((_PB_H+(-1*1))+(-1*c5))])
            ym1=0.0
            ym2=0.0
            xm1=0.0
            for c5 in range (_PB_H):
                (y1[c3])[c5]=((((a1*((imgIn[c3])[c5]))+(a2*xm1))+(b1*ym1))+(b2*ym2))
                (imgOut[c3])[c5]=(c1*(((y1[c3])[c5])+((y2[c3])[c5])))
                ym2=ym1
                ym1=((y1[c3])[c5])
                xm1=((imgIn[c3])[c5])
    if((_PB_H*-1>= 0)):
        for c3 in range (_PB_W):
            yp1=0.0
            yp2=0.0
            xp1=0.0
            xp2=0.0
            ym1=0.0
            ym2=0.0
            xm1=0.0
    for c3 in range (min(_PB_H , _PB_W)):
        tp1=0.0
        tp2=0.0
        yp1=0.0
        yp2=0.0
        for c5 in range (_PB_W + c3 * -1):
            (y2[((_PB_W+(-1*1))+(-1*c5))])[c3]=((((a7*tp1)+(a8*tp2))+(b1*yp1))+(b2*yp2))
            yp2=yp1
            yp1=((y2[((_PB_W+(-1*1))+(-1*c5))])[c3])
            tp2=tp1
            tp1=((imgOut[((_PB_W+(-1*1))+(-1*c5))])[c3])
        tm1=0.0
        ym1=0.0
        ym2=0.0
        for c5 in range (_PB_W):
            (y1[c5])[c3]=((((a5*((imgOut[c5])[c3]))+(a6*tm1))+(b1*ym1))+(b2*ym2))
            ym2=ym1
            ym1=((y1[c5])[c3])
            tm1=((imgOut[c5])[c3])
            (imgOut[c5])[c3]=(c2*(((y1[c5])[c3])+((y2[c5])[c3])))
    if((_PB_W-1>= 0)):
        for c3 in range (_PB_W , _PB_H):
            tp1=0.0
            tp2=0.0
            yp1=0.0
            yp2=0.0
            tm1=0.0
            ym1=0.0
            ym2=0.0
            for c5 in range (_PB_W):
                (y1[c5])[c3]=((((a5*((imgOut[c5])[c3]))+(a6*tm1))+(b1*ym1))+(b2*ym2))
                ym2=ym1
                ym1=((y1[c5])[c3])
                tm1=((imgOut[c5])[c3])
                (imgOut[c5])[c3]=(c2*(((y1[c5])[c3])+((y2[c5])[c3])))
    if((_PB_W*-1>= 0)):
        for c3 in range (_PB_H):
            tp1=0.0
            tp2=0.0
            yp1=0.0
            yp2=0.0
            tm1=0.0
            ym1=0.0
            ym2=0.0
    return (_PB_W,_PB_H,a1,a2,a3,a4,a5,a6,a7,a8,b1,b2,c1,c2,y1,y2,imgIn,imgOut)


def scop_nussinov(_PB_N, table, seq):
    raise NotImplementedError('FAlla el SCOP->C (no mete los ifs) luego falla PoCC')
    return (_PB_N, table, seq)

def scop_adi(_PB_TSTEPS,_PB_N,u,v,p,q,a,b,c,d,e,f):
    if((_PB_N*-1-1>= 0) and (_PB_TSTEPS-1>= 0)):
        if((_PB_N-3>= 0)):
            for c0 in range (1 , _PB_TSTEPS + 1):
                for c2 in range (1 , _PB_N * -1 + 1):
                    (v[(_PB_N+(-1*1))])[c2]=1.0
                    (p[c2])[0]=0.0
                for c2 in range (1 , _PB_N * -1 + 1):
                    for c7 in range (1 , _PB_N-1):
                        (p[c2])[c7]=((-1*c)/((a*((p[c2])[(c7+(-1*1))]))+b))
                for c2 in range (1 , _PB_N * -1 + 1):
                    (v[0])[c2]=1.0
                    (q[c2])[0]=((v[0])[c2])
                for c2 in range (1 , _PB_N * -1 + 1):
                    for c7 in range (1 , _PB_N-1):
                        (q[c2])[c7]=((((((-1*d)*((u[c7])[(c2+(-1*1))]))+((1.0+(2.0*d))*((u[c7])[c2])))+(-1*(f*((u[c7])[(c2+1)]))))+(-1*(a*((q[c2])[(c7+(-1*1))]))))/((a*((p[c2])[(c7+(-1*1))]))+b))
                for c2 in range (1 , _PB_N * -1 + 1):
                    (u[c2])[(_PB_N+(-1*1))]=1.0
                    (u[c2])[0]=1.0
                for c2 in range (1 , _PB_N * -1 + 1):
                    for c7 in range (_PB_N-1):
                        (v[((_PB_N+(-1*2))+(-1*c7))])[c2]=((((p[c2])[((_PB_N+(-1*2))+(-1*c7))])*((v[((_PB_N+(-1*1))+(-1*c7))])[c2]))+((q[c2])[((_PB_N+(-1*2))+(-1*c7))]))
                for c2 in range (1 , _PB_N * -1 + 1):
                    (p[c2])[0]=0.0
                    (q[c2])[0]=((u[c2])[0])
                for c2 in range (1 , _PB_N * -1 + 1):
                    for c7 in range (1 , _PB_N-1):
                        (p[c2])[c7]=((-1*f)/((d*((p[c2])[(c7+(-1*1))]))+e))
                    for c7 in range (1 , _PB_N-1):
                        (q[c2])[c7]=((((((-1*a)*((v[(c2+(-1*1))])[c7]))+((1.0+(2.0*a))*((v[c2])[c7])))+(-1*(c*((v[(c2+1)])[c7]))))+(-1*(d*((q[c2])[(c7+(-1*1))]))))/((d*((p[c2])[(c7+(-1*1))]))+e))
                    for c7 in range (_PB_N * -1 + 1):
                        (u[c2])[((_PB_N+(-1*2))+(-1*c7))]=((((p[c2])[((_PB_N+(-1*2))+(-1*c7))])*((u[c2])[((_PB_N+(-1*1))+(-1*c7))]))+((q[c2])[((_PB_N+(-1*2))+(-1*c7))]))
        if((_PB_N-2>= 0)):
            for c0 in range (1 , _PB_TSTEPS + 1):
                for c2 in range (1 , _PB_N * -1 + 1):
                    (v[(_PB_N+(-1*1))])[c2]=1.0
                    (p[c2])[0]=0.0
                for c2 in range (1 , _PB_N * -1 + 1):
                    (v[0])[c2]=1.0
                    (q[c2])[0]=((v[0])[c2])
                for c2 in range (1 , _PB_N * -1 + 1):
                    (u[c2])[(_PB_N+(-1*1))]=1.0
                    (u[c2])[0]=1.0
                for c2 in range (1 , _PB_N * -1 + 1):
                    (v[((_PB_N+(-1*2))+(-1*0))])[c2]=((((p[c2])[((_PB_N+(-1*2))+(-1*0))])*((v[((_PB_N+(-1*1))+(-1*0))])[c2]))+((q[c2])[((_PB_N+(-1*2))+(-1*0))]))
                for c2 in range (1 , _PB_N * -1 + 1):
                    (p[c2])[0]=0.0
                    (q[c2])[0]=((u[c2])[0])
                for c2 in range (1 , _PB_N * -1 + 1):
                    for c7 in range (_PB_N * -1 + 1):
                        (u[c2])[((_PB_N+(-1*2))+(-1*c7))]=((((p[c2])[((_PB_N+(-1*2))+(-1*c7))])*((u[c2])[((_PB_N+(-1*1))+(-1*c7))]))+((q[c2])[((_PB_N+(-1*2))+(-1*c7))]))
        if((_PB_N*-1+1>= 0)):
            for c0 in range (1 , _PB_TSTEPS + 1):
                for c2 in range (1 , _PB_N * -1 + 1):
                    (v[(_PB_N+(-1*1))])[c2]=1.0
                    (p[c2])[0]=0.0
                for c2 in range (1 , _PB_N * -1 + 1):
                    (v[0])[c2]=1.0
                    (q[c2])[0]=((v[0])[c2])
                for c2 in range (1 , _PB_N * -1 + 1):
                    (u[c2])[(_PB_N+(-1*1))]=1.0
                    (u[c2])[0]=1.0
                for c2 in range (1 , _PB_N * -1 + 1):
                    (p[c2])[0]=0.0
                    (q[c2])[0]=((u[c2])[0])
                for c2 in range (1 , _PB_N * -1 + 1):
                    for c7 in range (_PB_N * -1 + 1):
                        (u[c2])[((_PB_N+(-1*2))+(-1*c7))]=((((p[c2])[((_PB_N+(-1*2))+(-1*c7))])*((u[c2])[((_PB_N+(-1*1))+(-1*c7))]))+((q[c2])[((_PB_N+(-1*2))+(-1*c7))]))
    return (_PB_TSTEPS,_PB_N,u,v,p,q,a,b,c,d,e,f)

def scop_fdtd_2d(_PB_TMAX,_PB_NY,_PB_NX,_fict_,hz,ex,ey):
    if((_PB_NY-1>= 0) and (_PB_TMAX-1>= 0)):
        if((_PB_NX-2>= 0) and (_PB_NY-2>= 0)):
            for c0 in range (_PB_TMAX):
                (ey[0])[0]=(_fict_[c0])
                for c2 in range (c0 + 1 , _PB_NX + c0):
                    (ey[(-1 * c0) + c2])[0]=(((ey[(-1 * c0) + c2])[0])+(-1*(0.5*(((hz[(-1 * c0) + c2])[0])+(-1*((hz[((-1 * c0) + c2+(-1*1))])[0]))))))
                for c1 in range (c0 + 1 , _PB_NY + c0):
                    (ex[0])[(-1 * c0) + c1]=(((ex[0])[(-1 * c0) + c1])+(-1*(0.5*(((hz[0])[(-1 * c0) + c1])+(-1*((hz[0])[((-1 * c0) + c1+(-1*1))]))))))
                    (ey[0])[(-1 * c0) + c1]=(_fict_[c0])
                    for c2 in range (c0 + 1 , _PB_NX + c0):
                        (hz[((-1 * c0) + c2) + -1])[((-1 * c0) + c1) + -1]=(((hz[((-1 * c0) + c2) + -1])[((-1 * c0) + c1) + -1])+(-1*(0.7*(((((ex[((-1 * c0) + c2) + -1])[(((-1 * c0) + c1) + -1 +1)])+(-1*((ex[((-1 * c0) + c2) + -1])[((-1 * c0) + c1) + -1])))+((ey[(((-1 * c0) + c2) + -1 +1)])[((-1 * c0) + c1) + -1]))+(-1*((ey[((-1 * c0) + c2) + -1])[((-1 * c0) + c1) + -1]))))))
                        (ey[(-1 * c0) + c2])[(-1 * c0) + c1]=(((ey[(-1 * c0) + c2])[(-1 * c0) + c1])+(-1*(0.5*(((hz[(-1 * c0) + c2])[(-1 * c0) + c1])+(-1*((hz[((-1 * c0) + c2+(-1*1))])[(-1 * c0) + c1]))))))
                        (ex[(-1 * c0) + c2])[(-1 * c0) + c1]=(((ex[(-1 * c0) + c2])[(-1 * c0) + c1])+(-1*(0.5*(((hz[(-1 * c0) + c2])[(-1 * c0) + c1])+(-1*((hz[(-1 * c0) + c2])[((-1 * c0) + c1+(-1*1))]))))))
        if((_PB_NX-2>= 0)):
            for c0 in range (_PB_TMAX):
                (ey[0])[0]=(_fict_[c0])
                for c2 in range (c0 + 1 , _PB_NX + c0):
                    (ey[(-1 * c0) + c2])[0]=(((ey[(-1 * c0) + c2])[0])+(-1*(0.5*(((hz[(-1 * c0) + c2])[0])+(-1*((hz[((-1 * c0) + c2+(-1*1))])[0]))))))
        if((_PB_NX-1>= 0) and (_PB_NY-2>= 0)):
            for c0 in range (_PB_TMAX):
                (ey[0])[0]=(_fict_[c0])
                for c1 in range (c0 + 1 , _PB_NY + c0):
                    (ex[0])[(-1 * c0) + c1]=(((ex[0])[(-1 * c0) + c1])+(-1*(0.5*(((hz[0])[(-1 * c0) + c1])+(-1*((hz[0])[((-1 * c0) + c1+(-1*1))]))))))
                    (ey[0])[(-1 * c0) + c1]=(_fict_[c0])
        if((_PB_NX*-1+1>= 0)):
            for c0 in range (_PB_TMAX):
                (ey[0])[0]=(_fict_[c0])
        if((_PB_NX*-1>= 0) and (_PB_NY-2>= 0)):
            for c0 in range (_PB_TMAX):
                for c1 in range (c0 , _PB_NY + c0):
                    (ey[0])[(-1 * c0) + c1]=(_fict_[c0])
    return (_PB_TMAX,_PB_NY,_PB_NX,_fict_,hz,ex,ey)


def scop_head_3d(_PB_N, TSTEPS, A, B):
    if((TSTEPS-1>= 0) and (_PB_N-3>= 0)):
        for c0 in range (1 , TSTEPS + 1):
            for c2 in range (c0 * 2 + 1 , _PB_N + c0 * 2-1):
                for c3 in range (c0 * 2 + 1 , _PB_N + c0 * 2-1):
                    ((B[1])[(-2 * c0) + c2])[(-2 * c0) + c3]=((((0.125*(((((A[(1 +1)])[(-2 * c0) + c2])[(-2 * c0) + c3])+(-1*(2.0*(((A[1])[(-2 * c0) + c2])[(-2 * c0) + c3]))))+(((A[(1 +(-1*1))])[(-2 * c0) + c2])[(-2 * c0) + c3])))+(0.125*(((((A[1])[((-2 * c0) + c2+1)])[(-2 * c0) + c3])+(-1*(2.0*(((A[1])[(-2 * c0) + c2])[(-2 * c0) + c3]))))+(((A[1])[((-2 * c0) + c2+(-1*1))])[(-2 * c0) + c3]))))+(0.125*(((((A[1])[(-2 * c0) + c2])[((-2 * c0) + c3+1)])+(-1*(2.0*(((A[1])[(-2 * c0) + c2])[(-2 * c0) + c3]))))+(((A[1])[(-2 * c0) + c2])[((-2 * c0) + c3+(-1*1))]))))+(((A[1])[(-2 * c0) + c2])[(-2 * c0) + c3]))
            for c1 in range (c0 * 2 + 2 , _PB_N + c0 * 2-1):
                for c3 in range (c0 * 2 + 1 , _PB_N + c0 * 2-1):
                    ((B[(-2 * c0) + c1])[1])[(-2 * c0) + c3]=((((0.125*(((((A[((-2 * c0) + c1+1)])[1])[(-2 * c0) + c3])+(-1*(2.0*(((A[(-2 * c0) + c1])[1])[(-2 * c0) + c3]))))+(((A[((-2 * c0) + c1+(-1*1))])[1])[(-2 * c0) + c3])))+(0.125*(((((A[(-2 * c0) + c1])[(1 +1)])[(-2 * c0) + c3])+(-1*(2.0*(((A[(-2 * c0) + c1])[1])[(-2 * c0) + c3]))))+(((A[(-2 * c0) + c1])[(1 +(-1*1))])[(-2 * c0) + c3]))))+(0.125*(((((A[(-2 * c0) + c1])[1])[((-2 * c0) + c3+1)])+(-1*(2.0*(((A[(-2 * c0) + c1])[1])[(-2 * c0) + c3]))))+(((A[(-2 * c0) + c1])[1])[((-2 * c0) + c3+(-1*1))]))))+(((A[(-2 * c0) + c1])[1])[(-2 * c0) + c3]))
                for c2 in range (c0 * 2 + 2 , _PB_N + c0 * 2-1):
                    ((B[(-2 * c0) + c1])[(-2 * c0) + c2])[1]=((((0.125*(((((A[((-2 * c0) + c1+1)])[(-2 * c0) + c2])[1])+(-1*(2.0*(((A[(-2 * c0) + c1])[(-2 * c0) + c2])[1]))))+(((A[((-2 * c0) + c1+(-1*1))])[(-2 * c0) + c2])[1])))+(0.125*(((((A[(-2 * c0) + c1])[((-2 * c0) + c2+1)])[1])+(-1*(2.0*(((A[(-2 * c0) + c1])[(-2 * c0) + c2])[1]))))+(((A[(-2 * c0) + c1])[((-2 * c0) + c2+(-1*1))])[1]))))+(0.125*(((((A[(-2 * c0) + c1])[(-2 * c0) + c2])[(1 +1)])+(-1*(2.0*(((A[(-2 * c0) + c1])[(-2 * c0) + c2])[1]))))+(((A[(-2 * c0) + c1])[(-2 * c0) + c2])[(1 +(-1*1))]))))+(((A[(-2 * c0) + c1])[(-2 * c0) + c2])[1]))
                    for c3 in range (c0 * 2 + 2 , _PB_N + c0 * 2-1):
                        ((A[((-2 * c0) + c1) + -1])[((-2 * c0) + c2) + -1])[((-2 * c0) + c3) + -1]=((((0.125*(((((B[(((-2 * c0) + c1) + -1 +1)])[((-2 * c0) + c2) + -1])[((-2 * c0) + c3) + -1])+(-1*(2.0*(((B[((-2 * c0) + c1) + -1])[((-2 * c0) + c2) + -1])[((-2 * c0) + c3) + -1]))))+(((B[(((-2 * c0) + c1) + -1 +(-1*1))])[((-2 * c0) + c2) + -1])[((-2 * c0) + c3) + -1])))+(0.125*(((((B[((-2 * c0) + c1) + -1])[(((-2 * c0) + c2) + -1 +1)])[((-2 * c0) + c3) + -1])+(-1*(2.0*(((B[((-2 * c0) + c1) + -1])[((-2 * c0) + c2) + -1])[((-2 * c0) + c3) + -1]))))+(((B[((-2 * c0) + c1) + -1])[(((-2 * c0) + c2) + -1 +(-1*1))])[((-2 * c0) + c3) + -1]))))+(0.125*(((((B[((-2 * c0) + c1) + -1])[((-2 * c0) + c2) + -1])[(((-2 * c0) + c3) + -1 +1)])+(-1*(2.0*(((B[((-2 * c0) + c1) + -1])[((-2 * c0) + c2) + -1])[((-2 * c0) + c3) + -1]))))+(((B[((-2 * c0) + c1) + -1])[((-2 * c0) + c2) + -1])[(((-2 * c0) + c3) + -1 +(-1*1))]))))+(((B[((-2 * c0) + c1) + -1])[((-2 * c0) + c2) + -1])[((-2 * c0) + c3) + -1]))
                        ((B[(-2 * c0) + c1])[(-2 * c0) + c2])[(-2 * c0) + c3]=((((0.125*(((((A[((-2 * c0) + c1+1)])[(-2 * c0) + c2])[(-2 * c0) + c3])+(-1*(2.0*(((A[(-2 * c0) + c1])[(-2 * c0) + c2])[(-2 * c0) + c3]))))+(((A[((-2 * c0) + c1+(-1*1))])[(-2 * c0) + c2])[(-2 * c0) + c3])))+(0.125*(((((A[(-2 * c0) + c1])[((-2 * c0) + c2+1)])[(-2 * c0) + c3])+(-1*(2.0*(((A[(-2 * c0) + c1])[(-2 * c0) + c2])[(-2 * c0) + c3]))))+(((A[(-2 * c0) + c1])[((-2 * c0) + c2+(-1*1))])[(-2 * c0) + c3]))))+(0.125*(((((A[(-2 * c0) + c1])[(-2 * c0) + c2])[((-2 * c0) + c3+1)])+(-1*(2.0*(((A[(-2 * c0) + c1])[(-2 * c0) + c2])[(-2 * c0) + c3]))))+(((A[(-2 * c0) + c1])[(-2 * c0) + c2])[((-2 * c0) + c3+(-1*1))]))))+(((A[(-2 * c0) + c1])[(-2 * c0) + c2])[(-2 * c0) + c3]))
                    ((A[((-2 * c0) + c1) + -1])[((-2 * c0) + c2) + -1])[_PB_N + -2]=((((0.125*(((((B[(((-2 * c0) + c1) + -1 +1)])[((-2 * c0) + c2) + -1])[_PB_N + -2])+(-1*(2.0*(((B[((-2 * c0) + c1) + -1])[((-2 * c0) + c2) + -1])[_PB_N + -2]))))+(((B[(((-2 * c0) + c1) + -1 +(-1*1))])[((-2 * c0) + c2) + -1])[_PB_N + -2])))+(0.125*(((((B[((-2 * c0) + c1) + -1])[(((-2 * c0) + c2) + -1 +1)])[_PB_N + -2])+(-1*(2.0*(((B[((-2 * c0) + c1) + -1])[((-2 * c0) + c2) + -1])[_PB_N + -2]))))+(((B[((-2 * c0) + c1) + -1])[(((-2 * c0) + c2) + -1 +(-1*1))])[_PB_N + -2]))))+(0.125*(((((B[((-2 * c0) + c1) + -1])[((-2 * c0) + c2) + -1])[(_PB_N + -2 +1)])+(-1*(2.0*(((B[((-2 * c0) + c1) + -1])[((-2 * c0) + c2) + -1])[_PB_N + -2]))))+(((B[((-2 * c0) + c1) + -1])[((-2 * c0) + c2) + -1])[(_PB_N + -2 +(-1*1))]))))+(((B[((-2 * c0) + c1) + -1])[((-2 * c0) + c2) + -1])[_PB_N + -2]))
                for c3 in range (c0 * 2 + 2 , _PB_N + c0 * 2):
                    ((A[((-2 * c0) + c1) + -1])[_PB_N + -2])[((-2 * c0) + c3) + -1]=((((0.125*(((((B[(((-2 * c0) + c1) + -1 +1)])[_PB_N + -2])[((-2 * c0) + c3) + -1])+(-1*(2.0*(((B[((-2 * c0) + c1) + -1])[_PB_N + -2])[((-2 * c0) + c3) + -1]))))+(((B[(((-2 * c0) + c1) + -1 +(-1*1))])[_PB_N + -2])[((-2 * c0) + c3) + -1])))+(0.125*(((((B[((-2 * c0) + c1) + -1])[(_PB_N + -2 +1)])[((-2 * c0) + c3) + -1])+(-1*(2.0*(((B[((-2 * c0) + c1) + -1])[_PB_N + -2])[((-2 * c0) + c3) + -1]))))+(((B[((-2 * c0) + c1) + -1])[(_PB_N + -2 +(-1*1))])[((-2 * c0) + c3) + -1]))))+(0.125*(((((B[((-2 * c0) + c1) + -1])[_PB_N + -2])[(((-2 * c0) + c3) + -1 +1)])+(-1*(2.0*(((B[((-2 * c0) + c1) + -1])[_PB_N + -2])[((-2 * c0) + c3) + -1]))))+(((B[((-2 * c0) + c1) + -1])[_PB_N + -2])[(((-2 * c0) + c3) + -1 +(-1*1))]))))+(((B[((-2 * c0) + c1) + -1])[_PB_N + -2])[((-2 * c0) + c3) + -1]))
            for c2 in range (c0 * 2 + 2 , _PB_N + c0 * 2):
                for c3 in range (c0 * 2 + 2 , _PB_N + c0 * 2):
                    ((A[_PB_N + -2])[((-2 * c0) + c2) + -1])[((-2 * c0) + c3) + -1]=((((0.125*(((((B[(_PB_N + -2 +1)])[((-2 * c0) + c2) + -1])[((-2 * c0) + c3) + -1])+(-1*(2.0*(((B[_PB_N + -2])[((-2 * c0) + c2) + -1])[((-2 * c0) + c3) + -1]))))+(((B[(_PB_N + -2 +(-1*1))])[((-2 * c0) + c2) + -1])[((-2 * c0) + c3) + -1])))+(0.125*(((((B[_PB_N + -2])[(((-2 * c0) + c2) + -1 +1)])[((-2 * c0) + c3) + -1])+(-1*(2.0*(((B[_PB_N + -2])[((-2 * c0) + c2) + -1])[((-2 * c0) + c3) + -1]))))+(((B[_PB_N + -2])[(((-2 * c0) + c2) + -1 +(-1*1))])[((-2 * c0) + c3) + -1]))))+(0.125*(((((B[_PB_N + -2])[((-2 * c0) + c2) + -1])[(((-2 * c0) + c3) + -1 +1)])+(-1*(2.0*(((B[_PB_N + -2])[((-2 * c0) + c2) + -1])[((-2 * c0) + c3) + -1]))))+(((B[_PB_N + -2])[((-2 * c0) + c2) + -1])[(((-2 * c0) + c3) + -1 +(-1*1))]))))+(((B[_PB_N + -2])[((-2 * c0) + c2) + -1])[((-2 * c0) + c3) + -1]))
    return (_PB_N,TSTEPS,A,B)

def scop_jacobi_1D(_PB_TSTEPS,_PB_N,A,B):
    if((_PB_N-3>= 0) and (_PB_TSTEPS-1>= 0)):
        for c0 in range (_PB_TSTEPS):
            B[1]=(0.33333*(((A[(1 +(-1*1))])+(A[1]))+(A[(1 +1)])))
            for c1 in range (c0 * 2 + 2 , _PB_N + c0 * 2-1):
                B[(-2 * c0) + c1]=(0.33333*(((A[((-2 * c0) + c1+(-1*1))])+(A[(-2 * c0) + c1]))+(A[((-2 * c0) + c1+1)])))
                A[((-2 * c0) + c1) + -1]=(0.33333*(((B[(((-2 * c0) + c1) + -1 +(-1*1))])+(B[((-2 * c0) + c1) + -1]))+(B[(((-2 * c0) + c1) + -1 +1)])))
            A[_PB_N + -2]=(0.33333*(((B[(_PB_N + -2 +(-1*1))])+(B[_PB_N + -2]))+(B[(_PB_N + -2 +1)])))
    return (_PB_TSTEPS,_PB_N,A,B)


def scop_jacobi_2D(_PB_TSTEPS,_PB_N,A,B):
    if((_PB_N-3>= 0) and (_PB_TSTEPS-1>= 0)):
        for c0 in range (_PB_TSTEPS):
            for c2 in range (c0 * 2 + 1 , _PB_N + c0 * 2-1):
                (B[1])[(-2 * c0) + c2]=(0.2*((((((A[1])[(-2 * c0) + c2])+((A[1])[((-2 * c0) + c2+(-1*1))]))+((A[1])[(1+(-2 * c0) + c2)]))+((A[(1+1)])[(-2 * c0) + c2]))+((A[(1 +(-1*1))])[(-2 * c0) + c2])))
            for c1 in range (c0 * 2 + 2 , _PB_N + c0 * 2-1):
                (B[(-2 * c0) + c1])[1]=(0.2*((((((A[(-2 * c0) + c1])[1])+((A[(-2 * c0) + c1])[(1 +(-1*1))]))+((A[(-2 * c0) + c1])[(1+1)]))+((A[(1+(-2 * c0) + c1)])[1]))+((A[((-2 * c0) + c1+(-1*1))])[1])))
                for c2 in range (c0 * 2 + 2 , _PB_N + c0 * 2-1):
                    (A[((-2 * c0) + c1) + -1])[((-2 * c0) + c2) + -1]=(0.2*((((((B[((-2 * c0) + c1) + -1])[((-2 * c0) + c2) + -1])+((B[((-2 * c0) + c1) + -1])[(((-2 * c0) + c2) + -1 +(-1*1))]))+((B[((-2 * c0) + c1) + -1])[(1+((-2 * c0) + c2) + -1)]))+((B[(1+((-2 * c0) + c1) + -1)])[((-2 * c0) + c2) + -1]))+((B[(((-2 * c0) + c1) + -1 +(-1*1))])[((-2 * c0) + c2) + -1])))
                    (B[(-2 * c0) + c1])[(-2 * c0) + c2]=(0.2*((((((A[(-2 * c0) + c1])[(-2 * c0) + c2])+((A[(-2 * c0) + c1])[((-2 * c0) + c2+(-1*1))]))+((A[(-2 * c0) + c1])[(1+(-2 * c0) + c2)]))+((A[(1+(-2 * c0) + c1)])[(-2 * c0) + c2]))+((A[((-2 * c0) + c1+(-1*1))])[(-2 * c0) + c2])))
                (A[((-2 * c0) + c1) + -1])[_PB_N + -2]=(0.2*((((((B[((-2 * c0) + c1) + -1])[_PB_N + -2])+((B[((-2 * c0) + c1) + -1])[(_PB_N + -2 +(-1*1))]))+((B[((-2 * c0) + c1) + -1])[(1+_PB_N + -2)]))+((B[(1+((-2 * c0) + c1) + -1)])[_PB_N + -2]))+((B[(((-2 * c0) + c1) + -1 +(-1*1))])[_PB_N + -2])))
            for c2 in range (c0 * 2 + 2 , _PB_N + c0 * 2):
                (A[_PB_N + -2])[((-2 * c0) + c2) + -1]=(0.2*((((((B[_PB_N + -2])[((-2 * c0) + c2) + -1])+((B[_PB_N + -2])[(((-2 * c0) + c2) + -1 +(-1*1))]))+((B[_PB_N + -2])[(1+((-2 * c0) + c2) + -1)]))+((B[(1+_PB_N + -2)])[((-2 * c0) + c2) + -1]))+((B[(_PB_N + -2 +(-1*1))])[((-2 * c0) + c2) + -1])))
    return (_PB_TSTEPS,_PB_N,A,B)

def scop_seidel_2D(_PB_TSTEPS,_PB_N,A):
    if((_PB_N-3>= 0) and (_PB_TSTEPS-1>= 0)):
        for c0 in range (_PB_TSTEPS):
            for c1 in range (c0 + 1 , _PB_N + c0-1):
                for c2 in range (c0 + c1 + 1 , _PB_N + c0 + c1-1):
                    (A[(-1 * c0) + c1])[((-1 * c0) + (-1 * c1)) + c2]=(((((((((((A[((-1 * c0) + c1+(-1*1))])[(((-1 * c0) + (-1 * c1)) + c2+(-1*1))])+((A[((-1 * c0) + c1+(-1*1))])[((-1 * c0) + (-1 * c1)) + c2]))+((A[((-1 * c0) + c1+(-1*1))])[(((-1 * c0) + (-1 * c1)) + c2+1)]))+((A[(-1 * c0) + c1])[(((-1 * c0) + (-1 * c1)) + c2+(-1*1))]))+((A[(-1 * c0) + c1])[((-1 * c0) + (-1 * c1)) + c2]))+((A[(-1 * c0) + c1])[(((-1 * c0) + (-1 * c1)) + c2+1)]))+((A[((-1 * c0) + c1+1)])[(((-1 * c0) + (-1 * c1)) + c2+(-1*1))]))+((A[((-1 * c0) + c1+1)])[((-1 * c0) + (-1 * c1)) + c2]))+((A[((-1 * c0) + c1+1)])[(((-1 * c0) + (-1 * c1)) + c2+1)]))/9.0)
    return (_PB_TSTEPS,_PB_N,A)
