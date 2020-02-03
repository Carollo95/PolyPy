from math import sqrt


# Auxiliar funcions
def __max_score(s1, s2):
    if s1 >= s2:
        return s1
    return s2


def __match(b1, b2):
    if b1 + b2 == 3:
        return 1
    return 0


# DATAMINING
def scop_covariance(_PB_M, _PB_N, cov, mean, data, float_n):
    for j in range(_PB_M):
        mean[j] = (0.0)
        for i in range(_PB_N):
            mean[j] += data[i][j]
        mean[j] /= float_n
    for i in range(_PB_N):
        for j in range(_PB_M):
            data[i][j] -= mean[j]
    for i in range(_PB_M):
        for j in range(i, _PB_M):
            cov[i][j] = (0.0)
            for k in range(_PB_N):
                cov[i][j] += data[k][i] * data[k][j]
            cov[i][j] /= (float_n - (1.0))
            cov[j][i] = cov[i][j]

    return (_PB_M, _PB_N, cov, mean, data, float_n)


# LINEAR ALGEBRA
# BLAS
def scop_gemm(_PB_NI, _PB_NJ, _PB_NK, alpha, beta, A, B, C):
    for i in range(_PB_NI):
        for j in range(_PB_NJ):
            C[i][j] *= beta
        for k in range(_PB_NK):
            for j in range(_PB_NJ):
                C[i][j] += alpha * A[i][k] * B[k][j]

    return (_PB_NI, _PB_NJ, _PB_NK, alpha, beta, A, B, C)


def scop_gemver(_PB_N, alpha, beta, A, u1, u2, v1, v2, w, x, y, z):
    for i in range(_PB_N):
        for j in range(_PB_N):
            A[i][j] = A[i][j] + u1[i] * v1[j] + u2[i] * v2[j]
    for i in range(_PB_N):
        for j in range(_PB_N):
            x[i] = x[i] + beta * A[j][i] * y[j]
    for i in range(_PB_N):
        x[i] = x[i] + z[i]
    for i in range(_PB_N):
        for j in range(_PB_N):
            w[i] = w[i] + alpha * A[i][j] * x[j]

    return (_PB_N, alpha, beta, A, u1, u2, v1, v2, w, x, y, z)


def scop_gesummv(_PB_N, alpha, beta, A, B, tmp, x, y):
    for i in range(_PB_N):
        tmp[i] = (0.0)
        y[i] = (0.0)
        for j in range(_PB_N):
            tmp[i] = A[i][j] * x[j] + tmp[i]
            y[i] = B[i][j] * x[j] + y[i]
        y[i] = alpha * tmp[i] + beta * y[i]

    return (_PB_N, alpha, beta, A, B, tmp, x, y)


def scop_symm(_PB_N, _PB_M, alpha, beta, A, B, C):
    for i in range(_PB_M):
        for j in range(_PB_N):
            temp2 = 0
            for k in range(i):
                C[k][j] += alpha * B[i][j] * A[i][k]
                temp2 += B[k][j] * A[i][k]
            C[i][j] = beta * C[i][j] + alpha * B[i][j] * A[i][i] + alpha * temp2

    return (_PB_N, _PB_M, alpha, beta, A, B, C)


def scop_syr2k(_PB_N, _PB_M, alpha, beta, A, B, C):
    for i in range(_PB_N):
        for j in range(i + 1):
            C[i][j] *= beta
        for k in range(_PB_M):
            for j in range(i + 1):
                C[i][j] += A[j][k] * alpha * B[i][k] + B[j][k] * alpha * A[i][k]

    return (_PB_N, _PB_M, alpha, beta, A, B, C)


def scop_syrk(_PB_N, _PB_M, alpha, beta, A, C):
    for i in range(_PB_N):
        for j in range(i + 1):
            C[i][j] *= beta
        for k in range(_PB_M):
            for j in range(i + 1):
                C[i][j] += alpha * A[i][k] * A[j][k]

    return (_PB_N, _PB_M, alpha, beta, A, C)


def scop_trmm(_PB_N, _PB_M, alpha, A, B):
    for i in range(_PB_M):
        for j in range(_PB_N):
            for k in range(i + 1, _PB_M):
                B[i][j] += A[k][i] * B[k][j]
            B[i][j] = alpha * B[i][j]

    return (_PB_N, _PB_M, alpha, A, B)


# KERNELES

def scop_2mm(_PB_NI, _PB_NJ, _PB_NK, _PB_NL, tmp, alpha, beta, A, B, C, D):
    for i in range(_PB_NI):
        for j in range(_PB_NJ):
            tmp[i][j] = (0.0)
            for k in range(_PB_NK):
                tmp[i][j] += alpha * A[i][k] * B[k][j]
    for i in range(_PB_NI):
        for j in range(_PB_NL):
            D[i][j] *= beta
            for k in range(_PB_NJ):
                D[i][j] += tmp[i][k] * C[k][j]

    return (_PB_NI, _PB_NJ, _PB_NK, _PB_NL, tmp, alpha, beta, A, B, C, D)


def scop_3mm(_PB_NI, _PB_NJ, _PB_NK, _PB_NL, _PB_NM, A, B, C, D, E, F, G):
    for i in range(_PB_NI):
        for j in range(_PB_NJ):
            E[i][j] = (0.0)
            for k in range(_PB_NK):
                E[i][j] += A[i][k] * B[k][j]
    for i in range(_PB_NJ):
        for j in range(_PB_NL):
            F[i][j] = (0.0)
            for k in range(_PB_NM):
                F[i][j] += C[i][k] * D[k][j]
    for i in range(_PB_NI):
        for j in range(_PB_NL):
            G[i][j] = (0.0)
            for k in range(_PB_NJ):
                G[i][j] += E[i][k] * F[k][j]

    return (_PB_NI, _PB_NJ, _PB_NK, _PB_NL, _PB_NM, A, B, C, D, E, F, G)


def scop_atax(_PB_N, _PB_M, A, x, y, tmp):
    for i in range(_PB_N):
        y[i] = 0
    for i in range(_PB_M):
        tmp[i] = (0.0)
        for j in range(_PB_N):
            tmp[i] = tmp[i] + A[i][j] * x[j]
        for j in range(_PB_N):
            y[j] = y[j] + A[i][j] * tmp[i]

    return (_PB_N, _PB_M, A, x, y, tmp)


def scop_bicg(_PB_N, _PB_M, A, p, q, r, s):
    for i in range(_PB_M):
        s[i] = 0
    for i in range(_PB_N):
        q[i] = (0.0)
        for j in range(_PB_M):
            s[j] = s[j] + r[i] * A[i][j]
            q[i] = q[i] + A[i][j] * p[j]

    return (_PB_N, _PB_M, A, p, q, r, s)


def scop_doitgen(_PB_NR, _PB_NQ, _PB_NP, A, C4, suma):
    for r in range(_PB_NR):
        for q in range(_PB_NQ):
            for p in range(_PB_NP):
                suma[p] = (0.0)
                for s in range(_PB_NP):
                    suma[p] += A[r][q][s] * C4[s][p]
            for p in range(_PB_NP):
                A[r][q][p] = suma[p]

    return (_PB_NR, _PB_NQ, _PB_NP, A, C4, suma)


def scop_mvt(_PB_N, A, x1, x2, y_1, y_2):
    for i in range(_PB_N):
        for j in range(_PB_N):
            x1[i] = x1[i] + A[i][j] * y_1[j]
    for i in range(_PB_N):
        for j in range(_PB_N):
            x2[i] = x2[i] + A[j][i] * y_2[j]

    return (_PB_N, A, x1, x2, y_1, y_2)


# SOLVERS

def scop_cholesky(_PB_N, A, p):
    for i in range(_PB_N):
        for j in range(i):
            for k in range(j):
                A[i][j] -= A[i][k] * A[j][k]
            A[i][j] /= A[j][j]
        for k in range(i):
            A[i][i] -= A[i][k] * A[i][k]
        A[i][i] = sqrt(A[i][i])

    return (_PB_N, A, p)


def scop_durbin(_PB_N, alpha, beta, suma, y, r, z):
    for k in range(1, _PB_N):
        beta = (1 - alpha * alpha) * beta
        suma = (0.0)
        for i in range(k):
            suma += r[k - i - 1] * y[i]
        alpha = - (r[k] + suma) / beta
        for i in range(k):
            z[i] = y[i] + alpha * y[k - i - 1]
        for i in range(k):
            y[i] = z[i]
        y[k] = alpha

    return (_PB_N, alpha, beta, suma, y, r, z)


def scop_gramschmidt(_PB_N, _PB_M, A, Q, R):
    for k in range(_PB_N):
        nrm = (0.0)
        for i in range(_PB_M):
            nrm += A[i][k] * A[i][k]
        R[k][k] = sqrt(nrm)
        for i in range(_PB_M):
            Q[i][k] = A[i][k] / R[k][k]
        for j in range(k + 1, _PB_N):
            R[k][j] = (0.0)
            for i in range(_PB_M):
                R[k][j] += Q[i][k] * A[i][j]
            for i in range(_PB_M):
                A[i][j] = A[i][j] - Q[i][k] * R[k][j]

    return (_PB_N, _PB_M, A, Q, R)


def scop_lu(_PB_N, A):
    for i in range(_PB_N):
        for j in range(i):
            for k in range(j):
                A[i][j] -= A[i][k] * A[k][j]
            A[i][j] /= A[j][j]
        for j in range(i, _PB_N):
            for k in range(i):
                A[i][j] -= A[i][k] * A[k][j]

    return (_PB_N, A)


def scop_ludcmp(_PB_N, A, b, x, y):
    for i in range(_PB_N):
        for j in range(i):
            w = A[i][j]
            for k in range(j):
                w -= A[i][k] * A[k][j]
            A[i][j] = w / A[j][j]
        for j in range(i, _PB_N):
            w = A[i][j]
            for k in range(i):
                w -= A[i][k] * A[k][j]
            A[i][j] = w
    for i in range(_PB_N):
        w = b[i]
        for j in range(i):
            w -= A[i][j] * y[j]
        y[i] = w
    for i in range(_PB_N):
        w = y[_PB_N - 1]
        for j in range(_PB_N + i * -1 + 1, _PB_N):
            w -= A[_PB_N - i][j] * x[j]
        x[_PB_N - i - 1] = w / A[_PB_N - i - 1][_PB_N - i - 1]

    return (_PB_N, A, b, x, y)


def scop_trisolv(_PB_N, L, x, b):
    for i in range(_PB_N):
        x[i] = b[i]
        for j in range(i):
            x[i] -= L[i][j] * x[j]
        x[i] = x[i] / L[i][i]

    return (_PB_N, L, x, b)


# MEDLEY

def scop_deriche(_PB_W, _PB_H, a1, a2, a3, a4, a5, a6, a7, a8, b1, b2, c1, c2, y1, y2, imgIn, imgOut):
    for i in range(_PB_W):
        ym1 = (0.0)
        ym2 = (0.0)
        xm1 = (0.0)
        for j in range(_PB_H):
            y1[i][j] = a1 * imgIn[i][j] + a2 * xm1 + b1 * ym1 + b2 * ym2
            xm1 = imgIn[i][j]
            ym2 = ym1
            ym1 = y1[i][j]
    for i in range(_PB_W):
        yp1 = (0.0)
        yp2 = (0.0)
        xp1 = (0.0)
        xp2 = (0.0)
        for j in range(_PB_H):
            y2[i][_PB_H - 1 - j] = a3 * xp1 + a4 * xp2 + b1 * yp1 + b2 * yp2
            xp2 = xp1
            xp1 = imgIn[i][_PB_H - 1 - j]
            yp2 = yp1
            yp1 = y2[i][_PB_H - 1 - j]
    for i in range(_PB_W):
        for j in range(_PB_H):
            imgOut[i][j] = c1 * (y1[i][j] + y2[i][j])
    for j in range(_PB_H):
        tm1 = (0.0)
        ym1 = (0.0)
        ym2 = (0.0)
        for i in range(_PB_W):
            y1[i][j] = a5 * imgOut[i][j] + a6 * tm1 + b1 * ym1 + b2 * ym2
            tm1 = imgOut[i][j]
            ym2 = ym1
            ym1 = y1[i][j]
    for j in range(_PB_H):
        tp1 = (0.0)
        tp2 = (0.0)
        yp1 = (0.0)
        yp2 = (0.0)
        for i in range(_PB_W + j * -1):
            y2[_PB_W - 1 - i][j] = a7 * tp1 + a8 * tp2 + b1 * yp1 + b2 * yp2
            tp2 = tp1
            tp1 = imgOut[_PB_W - 1 - i][j]
            yp2 = yp1
            yp1 = y2[_PB_W - 1 - i][j]
    for i in range(_PB_W):
        for j in range(_PB_H):
            imgOut[i][j] = c2 * (y1[i][j] + y2[i][j])

    return (_PB_W, _PB_H, a1, a2, a3, a4, a5, a6, a7, a8, b1, b2, c1, c2, y1, y2, imgIn, imgOut)


def scop_nussinov(_PB_N, table, seq):
    for i in range(_PB_N):
        for j in range(_PB_N + i * -1, _PB_N):
            if j - 1 >= 0:
                table[_PB_N - 1 - i][j] = __max_score(table[_PB_N - 1 - i][j], table[_PB_N - 1 - i][j - 1])
            if i - 1 >= 0:
                table[_PB_N - 1 - i][j] = __max_score(table[_PB_N - 1 - i][j], table[_PB_N - i][j])
            if i - 1 >= 0 and j - 1 >= 0 and _PB_N * -1 + i + j - 1 >= 0:
                table[_PB_N - 1 - i][j] = __max_score(table[_PB_N - 1 - i][j],
                                                      table[_PB_N - i][j - 1] + __match(seq[_PB_N - 1 - i], seq[j]))
            if i - 1 >= 0 and j - 1 >= 0 and _PB_N + i * -1 + j * -1 >= 0:
                table[_PB_N - 1 - i][j] = __max_score(table[_PB_N - 1 - i][j], table[_PB_N - i][j - 1])
            for k in range(_PB_N + i * -1, j):
                table[_PB_N - 1 - i][j] = __max_score(table[_PB_N - 1 - i][j], table[_PB_N - 1 - i][k] + table[k + 1][j])
    return (_PB_N, table, seq)


# STENCILS

def scop_adi(_PB_TSTEPS, _PB_N, u, v, p, q, a, b, c, d, e, f):
    for t in range(1, _PB_TSTEPS + 1):
        for i in range(1, _PB_N - 1):
            v[0][i] = (1.0)
            p[i][0] = (0.0)
            q[i][0] = v[0][i]
            for j in range(1, _PB_N + -1):
                p[i][j] = -c / (a * p[i][j - 1] + b)
                q[i][j] = (-d * u[j][i - 1] + ((1.0) + (2.0) * d) * u[j][i] - f * u[j][i + 1] - a * q[i][j - 1]) / (
                            a * p[i][j - 1] + b)
            v[_PB_N - 1][i] = (1.0)
            for j in range(_PB_N + -1):
                v[_PB_N - 2 - j][i] = p[i][_PB_N - 2 - j] * v[_PB_N - 1 - j][i] + q[i][_PB_N - 2 - j]
        for i in range(1, _PB_N - 1):
            u[i][0] = (1.0)
            p[i][0] = (0.0)
            q[i][0] = u[i][0]
            for j in range(1, _PB_N + -1):
                p[i][j] = -f / (d * p[i][j - 1] + e)
                q[i][j] = (-a * v[i - 1][j] + ((1.0) + (2.0) * a) * v[i][j] - c * v[i + 1][j] - d * q[i][j - 1]) / (
                            d * p[i][j - 1] + e)
            u[i][_PB_N - 1] = (1.0)
            for j in range(_PB_N - 1):
                u[i][_PB_N - 2 - j] = p[i][_PB_N - 2 - j] * u[i][_PB_N - 1 - j] + q[i][_PB_N - 2 - j]

    return (_PB_TSTEPS, _PB_N, u, v, p, q, a, b, c, d, e, f)


def scop_fdtd_2d(_PB_TMAX, _PB_NY, _PB_NX, _fict_, hz, ex, ey):
    for t in range(_PB_TMAX):
        for j in range(_PB_NY):
            ey[0][j] = _fict_[t]
        for i in range(1, _PB_NX):
            for j in range(_PB_NY):
                ey[i][j] = ey[i][j] - (0.5) * (hz[i][j] - hz[i - 1][j])
        for i in range(_PB_NX):
            for j in range(1, _PB_NY):
                ex[i][j] = ex[i][j] - (0.5) * (hz[i][j] - hz[i][j - 1])
        for i in range(_PB_NX + -1):
            for j in range(_PB_NY + -1):
                hz[i][j] = hz[i][j] - (0.7) * (ex[i][j + 1] - ex[i][j] + ey[i + 1][j] - ey[i][j])

    return (_PB_TMAX, _PB_NY, _PB_NX, _fict_, hz, ex, ey)


def scop_head_3d(_PB_N, TSTEPS, A, B):
    for t in range(1, TSTEPS + 1):
        for i in range(1, _PB_N + -1):
            for j in range(1, _PB_N + -1):
                for k in range(1, _PB_N + -1):
                    B[i][j][k] = (0.125) * (A[i + 1][j][k] - (2.0) * A[i][j][k] + A[i - 1][j][k]) + (0.125) * (
                                A[i][j + 1][k] - (2.0) * A[i][j][k] + A[i][j - 1][k]) + (0.125) * (
                                             A[i][j][k + 1] - (2.0) * A[i][j][k] + A[i][j][k - 1]) + A[i][j][k]
        for i in range(1, _PB_N + -1):
            for j in range(1, _PB_N + -1):
                for k in range(1, _PB_N + -1):
                    A[i][j][k] = (0.125) * (B[i + 1][j][k] - (2.0) * B[i][j][k] + B[i - 1][j][k]) + (0.125) * (
                                B[i][j + 1][k] - (2.0) * B[i][j][k] + B[i][j - 1][k]) + (0.125) * (
                                             B[i][j][k + 1] - (2.0) * B[i][j][k] + B[i][j][k - 1]) + B[i][j][k]

    return (_PB_N, TSTEPS, A, B)


def scop_jacobi_1D(_PB_TSTEPS, _PB_N, A, B):
    for t in range(_PB_TSTEPS):
        for i in range(1, _PB_N + -1):
            B[i] = 0.33333 * (A[i - 1] + A[i] + A[i + 1])
        for i in range(1, _PB_N + -1):
            A[i] = 0.33333 * (B[i - 1] + B[i] + B[i + 1])

    return (_PB_TSTEPS, _PB_N, A, B)


def scop_jacobi_2D(_PB_TSTEPS, _PB_N, A, B):
    for t in range(_PB_TSTEPS):
        for i in range(1, _PB_N + -1):
            for j in range(1, _PB_N + -1):
                B[i][j] = (0.2) * (A[i][j] + A[i][j - 1] + A[i][1 + j] + A[1 + i][j] + A[i - 1][j])
        for i in range(1, _PB_N + -1):
            for j in range(1, _PB_N + -1):
                A[i][j] = (0.2) * (B[i][j] + B[i][j - 1] + B[i][1 + j] + B[1 + i][j] + B[i - 1][j])

    return (_PB_TSTEPS, _PB_N, A, B)


def scop_seidel_2D(_PB_TSTEPS, _PB_N, A):
    for t in range(_PB_TSTEPS):
        for i in range(1, _PB_N + -1):
            for j in range(1, _PB_N + -1):
                A[i][j] = (A[i - 1][j - 1] + A[i - 1][j] + A[i - 1][j + 1] + A[i][j - 1] + A[i][j] + A[i][j + 1] +
                           A[i + 1][j - 1] + A[i + 1][j] + A[i + 1][j + 1]) / (9.0)

    return (_PB_TSTEPS, _PB_N, A)
