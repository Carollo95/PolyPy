from math import e


# AUX
def __empty_list_1D(n):
    return [None] * n


def __empty_list_2D(n, m):
    return list(__empty_list_1D(m) for i in range(n))


def __empty_list_3D(n, m, o):
    return list(__empty_list_2D(m, o) for i in range(n))


MINI_DATA_SET = 0
SMALL_DATA_SET = 1
STANDARD_DATA_SET = 2
LARGE_DATA_SET = 3
EXTRA_LARGE_DATA_SET = 4


# DATAMINING
def benchmark_covariance(dataset, use_optimized_benchmark=False, return_result=False):
    if dataset == MINI_DATA_SET:
        m = 32
        n = 28
    elif dataset == SMALL_DATA_SET:
        m = 80
        n = 100
    elif dataset == LARGE_DATA_SET:
        m = 1200
        n = 1400
    elif dataset == EXTRA_LARGE_DATA_SET:
        m = 2600
        n = 300
    else:
        m = 240
        n = 260

    data = __empty_list_2D(n, m)
    cov = __empty_list_2D(m, m)
    mean = __empty_list_1D(m)
    float_n = n

    for i in range(n):
        for j in range(m):
            data[i][j] = (i * j) / m

    # Function dependency injection
    if use_optimized_benchmark:
        import optimized_benchmark_functions as bf
    else:
        import benchmark_functions as bf

    result = bf.scop_covariance(m, n, cov, mean, data, float_n)

    if return_result:
        return result


# LINEAR ALGEBRA
# BLAS
def benchmark_gemm(dataset, use_optimized_benchmark=False, return_result=False):
    if dataset == MINI_DATA_SET:
        ni = 20
        nj = 25
        nk = 30
    elif dataset == SMALL_DATA_SET:
        ni = 60
        nj = 70
        nk = 80
    elif dataset == LARGE_DATA_SET:
        ni = 1000
        nj = 1100
        nk = 1200
    elif dataset == EXTRA_LARGE_DATA_SET:
        ni = 2000
        nj = 2300
        nk = 2600
    else:
        ni = 200
        nj = 220
        nk = 240

    alpha = 1.5
    beta = 1.2
    A = __empty_list_2D(ni, nk)
    B = __empty_list_2D(nk, nj)
    C = __empty_list_2D(ni, nj)

    for i in range(ni):
        for j in range(nj):
            C[i][j] = ((i * j + 1) % ni) / ni
    for i in range(ni):
        for j in range(nk):
            A[i][j] = ((i * j + 1) % nk) / nk
    for i in range(nk):
        for j in range(nj):
            B[i][j] = ((i * j + 1) % nj) / nj

    # Function dependency injection
    if use_optimized_benchmark:
        import optimized_benchmark_functions as bf
    else:
        import benchmark_functions as bf

    result = bf.scop_gemm(ni, nj, nk, alpha, beta, A, B, C)

    if return_result:
        return result


def benchmark_gemerv(dataset, use_optimized_benchmark=False, return_result=False):
    if dataset == MINI_DATA_SET:
        n = 40
    elif dataset == SMALL_DATA_SET:
        n = 120
    elif dataset == LARGE_DATA_SET:
        n = 2000
    elif dataset == EXTRA_LARGE_DATA_SET:
        n = 4000
    else:
        n = 400

    alpha = 1.5
    beta = 1.2
    A = __empty_list_2D(n, n)
    u1 = __empty_list_1D(n)
    u2 = __empty_list_1D(n)
    v1 = __empty_list_1D(n)
    v2 = __empty_list_1D(n)
    w = __empty_list_1D(n)
    x = __empty_list_1D(n)
    y = __empty_list_1D(n)
    z = __empty_list_1D(n)

    for i in range(n):
        u1[i] = i
        u2[i] = ((i + 1) / n) / 2.0
        v1[i] = ((i + 1) / n) / 4.0
        v2[i] = ((i + 1) / n) / 6.0
        y[i] = ((i + 1) / n) / 8.0
        z[i] = ((i + 1) / n) / 9.0
        x[i] = 0.0
        w[i] = 0.0
        for j in range(n):
            A[i][j] = (i * j % n) / n

    # Function dependency injection
    if use_optimized_benchmark:
        import optimized_benchmark_functions as bf
    else:
        import benchmark_functions as bf

    result = bf.scop_gemver(n, alpha, beta, A, u1, u2, v1, v2, w, x, y, z)
    if return_result:
        return result


def benchmark_gesummv(dataset, use_optimized_benchmark=False, return_result=False):
    if dataset == MINI_DATA_SET:
        n = 30
    elif dataset == SMALL_DATA_SET:
        n = 90
    elif dataset == LARGE_DATA_SET:
        n = 1300
    elif dataset == EXTRA_LARGE_DATA_SET:
        n = 2800
    else:
        n = 2800

    alpha = 1.5
    beta = 1.2
    A = __empty_list_2D(n, n)
    B = __empty_list_2D(n, n)
    tmp = __empty_list_1D(n)
    x = __empty_list_1D(n)
    y = __empty_list_1D(n)

    for i in range(n):
        x[i] = (i % n) / n
        for j in range(n):
            A[i][j] = ((i * j + 1) % n) / n
            B[i][j] = ((i * j + 2) % n) / n

    # Function dependency injection
    if use_optimized_benchmark:
        import optimized_benchmark_functions as bf
    else:
        import benchmark_functions as bf

    result = bf.scop_gesummv(n, alpha, beta, A, B, tmp, x, y)
    if return_result:
        return result


def benchmark_symm(dataset, use_optimized_benchmark=False, return_result=False):
    if dataset == MINI_DATA_SET:
        m = 20
        n = 30
    elif dataset == SMALL_DATA_SET:
        m = 60
        n = 80
    elif dataset == LARGE_DATA_SET:
        m = 1000
        n = 1200
    elif dataset == EXTRA_LARGE_DATA_SET:
        m = 2000
        n = 2600
    else:
        m = 200
        n = 240

    alpha = 1.5
    beta = 1.2
    A = __empty_list_2D(m, m)
    B = __empty_list_2D(m, n)
    C = __empty_list_2D(m, n)

    for i in range(m):
        for j in range(n):
            C[i][j] = ((i + j) % 100) / m
            B[i][j] = ((n + i - j) % 100) / m
    for i in range(m):
        for j in range(i + 1):
            A[i][j] = ((i + j) % 100) / m

    # Function dependency injection
    if use_optimized_benchmark:
        import optimized_benchmark_functions as bf
    else:
        import benchmark_functions as bf

    result = bf.scop_symm(n, m, alpha, beta, A, B, C)
    if return_result:
        return result


def benchmark_syr2k(dataset, use_optimized_benchmark=False, return_result=False):
    if dataset == MINI_DATA_SET:
        m = 20
        n = 30
    elif dataset == SMALL_DATA_SET:
        m = 60
        n = 80
    elif dataset == LARGE_DATA_SET:
        m = 1000
        n = 1200
    elif dataset == EXTRA_LARGE_DATA_SET:
        m = 2000
        n = 2600
    else:
        m = 200
        n = 240

    alpha = 1.5
    beta = 1.2
    A = __empty_list_2D(n, m)
    B = __empty_list_2D(n, m)
    C = __empty_list_2D(n, n)

    for i in range(n):
        for j in range(m):
            A[i][j] = ((i * j + 1) % n) / n
            B[i][j] = ((i * j + 2) % m) / m
    for i in range(n):
        for j in range(n):
            C[i][j] = ((i * j + 3) % n) / m

    # Function dependency injection
    if use_optimized_benchmark:
        import optimized_benchmark_functions as bf
    else:
        import benchmark_functions as bf

    result = bf.scop_syr2k(n, m, alpha, beta, A, B, C)
    if return_result:
        return result


def benchmark_syrk(dataset, use_optimized_benchmark=False, return_result=False):
    if dataset == MINI_DATA_SET:
        m = 20
        n = 30
    elif dataset == SMALL_DATA_SET:
        m = 60
        n = 80
    elif dataset == LARGE_DATA_SET:
        m = 1000
        n = 1200
    elif dataset == EXTRA_LARGE_DATA_SET:
        m = 2000
        n = 2600
    else:
        m = 200
        n = 240

    alpha = 1.5
    beta = 1.2
    A = __empty_list_2D(n, m)
    C = __empty_list_2D(n, n)

    for i in range(n):
        for j in range(m):
            A[i][j] = ((i * j + 1) % n) / n
    for i in range(n):
        for j in range(n):
            C[i][j] = ((i * j + 2) % m) / m

    # Function dependency injection
    if use_optimized_benchmark:
        import optimized_benchmark_functions as bf
    else:
        import benchmark_functions as bf

    result = bf.scop_syrk(n, m, alpha, beta, A, C)
    if return_result:
        return result


def benchmark_trmm(dataset, use_optimized_benchmark=False, return_result=False):
    if dataset == MINI_DATA_SET:
        n = 20
        m = 30
    elif dataset == SMALL_DATA_SET:
        n = 60
        m = 80
    elif dataset == LARGE_DATA_SET:
        n = 1000
        m = 1200
    elif dataset == EXTRA_LARGE_DATA_SET:
        n = 2000
        m = 2600
    else:
        n = 200
        m = 240

    alpha = 1.5
    A = __empty_list_2D(m, m)
    B = __empty_list_2D(m, n)

    for i in range(m):
        for j in range(i):
            A[i][j] = ((i + j) % m) / m
        for j in range(n):
            B[i][j] = ((n + (i - j)) % n) / n

    # Function dependency injection
    if use_optimized_benchmark:
        import optimized_benchmark_functions as bf
    else:
        import benchmark_functions as bf

    result = bf.scop_trmm(n, n, alpha, A, B)
    if return_result:
        return result


# KERNELES
def benchmark_2mm(dataset, use_optimized_benchmark=False, return_result=False):
    if dataset == MINI_DATA_SET:
        ni = 16
        nj = 18
        nk = 22
        nl = 24
    elif dataset == SMALL_DATA_SET:
        ni = 40
        nj = 50
        nk = 70
        nl = 80
    elif dataset == LARGE_DATA_SET:
        ni = 800
        nj = 900
        nk = 1100
        nl = 1200
    elif dataset == EXTRA_LARGE_DATA_SET:
        ni = 1600
        nj = 1800
        nk = 2200
        nl = 2400
    else:
        ni = 180
        nj = 190
        nk = 210
        nl = 220

    alpha = 1.5
    beta = 1.2
    A = __empty_list_2D(ni, nk)
    B = __empty_list_2D(nk, nj)
    C = __empty_list_2D(nj, nl)
    D = __empty_list_2D(ni, nl)
    tmp = __empty_list_2D(ni, nj)

    for i in range(ni):
        for j in range(nk):
            A[i][j] = ((i * j + 1) % ni) / ni
    for i in range(nk):
        for j in range(nj):
            B[i][j] = (i * (j + 1) % nj) / nj
    for i in range(nj):
        for j in range(nl):
            C[i][j] = ((i * (j + 3) + 1) % nl) / nl
    for i in range(ni):
        for j in range(nl):
            D[i][j] = (i * (j + 2) % nk) / nk

    # Function dependency injection
    if use_optimized_benchmark:
        import optimized_benchmark_functions as bf
    else:
        import benchmark_functions as bf

    result = bf.scop_2mm(ni, nj, nk, nl, tmp, alpha, beta, A, B, C, D)
    if return_result:
        return result


def benchmark_3mm(dataset, use_optimized_benchmark=False, return_result=False):
    if dataset == MINI_DATA_SET:
        ni = 16
        nj = 18
        nk = 20
        nl = 22
        nm = 24
    elif dataset == SMALL_DATA_SET:
        ni = 40
        nj = 50
        nk = 60
        nl = 70
        nm = 80
    elif dataset == LARGE_DATA_SET:
        ni = 800
        nj = 900
        nk = 1000
        nl = 1100
        nm = 1200
    elif dataset == EXTRA_LARGE_DATA_SET:
        ni = 1600
        nj = 1800
        nk = 2000
        nl = 2200
        nm = 2400
    else:
        ni = 180
        nj = 190
        nk = 200
        nl = 210
        nm = 220

    A = __empty_list_2D(ni, nk)
    B = __empty_list_2D(nk, nj)
    C = __empty_list_2D(nj, nm)
    D = __empty_list_2D(nm, nl)
    E = __empty_list_2D(ni, nj)
    F = __empty_list_2D(nj, nl)
    G = __empty_list_2D(ni, nl)

    for i in range(ni):
        for j in range(nk):
            A[i][j] = ((i * j + 1) % ni) / (5 * ni)
    for i in range(nk):
        for j in range(nj):
            B[i][j] = ((i * (j + 1) + 2) % nj) / (5 * nj)
    for i in range(nj):
        for j in range(nm):
            C[i][j] = (i * (j + 3) % nl) / (5 * nl)
    for i in range(nm):
        for j in range(nl):
            D[i][j] = ((i * (j + 2) + 2) % nk) / (5 * nk)

    # Function dependency injection
    if use_optimized_benchmark:
        import optimized_benchmark_functions as bf
    else:
        import benchmark_functions as bf

    result = bf.scop_3mm(ni, nj, nk, nl, nm, A, B, C, D, E, F, G)
    if return_result:
        return result


def benchmark_atax(dataset, use_optimized_benchmark=False, return_result=False):
    if dataset == MINI_DATA_SET:
        m = 38
        n = 42
    elif dataset == SMALL_DATA_SET:
        m = 116
        n = 124
    elif dataset == LARGE_DATA_SET:
        m = 1900
        n = 2100
    elif dataset == EXTRA_LARGE_DATA_SET:
        m = 1800
        n = 2200
    else:
        m = 390
        n = 410

    A = __empty_list_2D(m, n)
    x = __empty_list_1D(n)
    y = __empty_list_1D(n)
    tmp = __empty_list_1D(m)

    for i in range(n):
        x[i] = 1 + (i / n)
    for i in range(m):
        for j in range(n):
            A[i][j] = ((i + j) % n) / (5 * m)

    # Function dependency injection
    if use_optimized_benchmark:
        import optimized_benchmark_functions as bf
    else:
        import benchmark_functions as bf

    result = bf.scop_atax(n, m, A, x, y, tmp)
    if return_result:
        return result


def benchmark_bicg(dataset, use_optimized_benchmark=False, return_result=False):
    if dataset == MINI_DATA_SET:
        m = 38
        n = 42
    elif dataset == SMALL_DATA_SET:
        m = 116
        n = 124
    elif dataset == LARGE_DATA_SET:
        m = 1900
        n = 2100
    elif dataset == EXTRA_LARGE_DATA_SET:
        m = 1800
        n = 2200
    else:
        m = 390
        n = 410

    A = __empty_list_2D(n, m)
    s = __empty_list_1D(m)
    q = __empty_list_1D(n)
    p = __empty_list_1D(m)
    r = __empty_list_1D(n)

    for i in range(m):
        p[i] = (i % m) / m
    for i in range(n):
        r[i] = (i % n) / n
        for j in range(m):
            A[i][j] = (i * (j + 1) % n) / n

    # Function dependency injection
    if use_optimized_benchmark:
        import optimized_benchmark_functions as bf
    else:
        import benchmark_functions as bf

    result = bf.scop_bicg(n, m, A, p, q, r, s)
    if return_result:
        return result


def benchmark_doitgen(dataset, use_optimized_benchmark=False, return_result=False):
    if dataset == MINI_DATA_SET:
        nq = 8
        nr = 10
        np = 12
    elif dataset == SMALL_DATA_SET:
        nq = 20
        nr = 25
        np = 30
    elif dataset == LARGE_DATA_SET:
        nq = 140
        nr = 150
        np = 160
    elif dataset == EXTRA_LARGE_DATA_SET:
        nq = 220
        nr = 250
        np = 270
    else:
        nq = 40
        nr = 50
        np = 60

    A = __empty_list_3D(nr, nq, np)
    C4 = __empty_list_2D(np, np)
    suma = __empty_list_1D(np)

    for i in range(nr):
        for j in range(nq):
            for k in range(np):
                A[i][j][k] = ((i * j + k) % np) / np
    for i in range(np):
        for j in range(np):
            C4[i][j] = (i * j % np) / np

    # Function dependency injection
    if use_optimized_benchmark:
        import optimized_benchmark_functions as bf
    else:
        import benchmark_functions as bf

    result = bf.scop_doitgen(nr, nq, np, A, C4, suma)
    if return_result:
        return result


def benchmark_mvt(dataset, use_optimized_benchmark=False, return_result=False):
    if dataset == MINI_DATA_SET:
        n = 40
    elif dataset == SMALL_DATA_SET:
        n = 120
    elif dataset == LARGE_DATA_SET:
        n = 2000
    elif dataset == EXTRA_LARGE_DATA_SET:
        n = 4000
    else:
        n = 400

    A = __empty_list_2D(n, n)
    x1 = __empty_list_1D(n)
    x2 = __empty_list_1D(n)
    y_1 = __empty_list_1D(n)
    y_2 = __empty_list_1D(n)

    for i in range(n):
        x1[i] = (i % n) / n
        x2[i] = ((i + 1) % n) / n
        y_1[i] = ((i + 3) % n) / n
        y_2[i] = ((i + 4) % n) / n
        for j in range(n):
            A[i][j] = (i * j % n) / n

    # Function dependency injection
    if use_optimized_benchmark:
        import optimized_benchmark_functions as bf
    else:
        import benchmark_functions as bf

    result = bf.scop_mvt(n, A, x1, x2, y_1, y_2)
    if return_result:
        return result


def benchmark_cholesky(dataset, use_optimized_benchmark=False, return_result=False):
    if dataset == MINI_DATA_SET:
        n = 40
    elif dataset == SMALL_DATA_SET:
        n = 120
    elif dataset == LARGE_DATA_SET:
        n = 2000
    elif dataset == EXTRA_LARGE_DATA_SET:
        n = 4000
    else:
        n = 400

    A = __empty_list_2D(n, n)
    p = __empty_list_1D(n)

    for i in range(n):
        for j in range(i + 1):
            A[i][j] = (-j % n) / n + 1
        for j in range(i + 1, n):
            A[i][j] = 0
        A[i][j] = 1

    B = __empty_list_2D(n, n)
    for r in range(n):
        for s in range(n):
            B[r][s] = 0
    for t in range(n):
        for r in range(n):
            for s in range(n):
                B[r][s] += A[r][t] * A[s][t]
        for r in range(n):
            for s in range(n):
                A[r][s] = B[r][s]

    # Function dependency injection
    if use_optimized_benchmark:
        import optimized_benchmark_functions as bf
    else:
        import benchmark_functions as bf

    result = bf.scop_cholesky(n, A, p)
    if return_result:
        return result


def benchmark_durbin(dataset, use_optimized_benchmark=False, return_result=False):
    if dataset == MINI_DATA_SET:
        n = 40
    elif dataset == SMALL_DATA_SET:
        n = 120
    elif dataset == LARGE_DATA_SET:
        n = 2000
    elif dataset == EXTRA_LARGE_DATA_SET:
        n = 4000
    else:
        n = 400

    suma = __empty_list_2D(n, n)
    y = __empty_list_1D(n)
    z = __empty_list_1D(n)
    r = __empty_list_1D(n)

    for i in range(n):
        r[i] = (n + 1 - i)

    y[0] = -1 * r[0]
    beta = 1.0
    alpha = -1 * r[0]

    # Function dependency injection
    if use_optimized_benchmark:
        import optimized_benchmark_functions as bf
    else:
        import benchmark_functions as bf

    result = bf.scop_durbin(n, alpha, beta, suma, y, r, z)
    if return_result:
        return result


def benchmark_gramschmidt(dataset, use_optimized_benchmark=False, return_result=False):
    if dataset == MINI_DATA_SET:
        m = 20
        n = 30
    elif dataset == SMALL_DATA_SET:
        m = 60
        n = 80
    elif dataset == LARGE_DATA_SET:
        m = 1000
        n = 1200
    elif dataset == EXTRA_LARGE_DATA_SET:
        m = 2000
        n = 2600
    else:
        m = 200
        n = 240

    A = __empty_list_2D(m, n)
    Q = __empty_list_2D(m, n)
    R = __empty_list_2D(n, n)

    for i in range(m):
        for j in range(n):
            A[i][j] = ((((i * j) % m) / m) * 100) + 10
            Q[i][j] = 0.0
    for i in range(n):
        for j in range(n):
            R[i][j] = 0.0

    # Function dependency injection
    if use_optimized_benchmark:
        import optimized_benchmark_functions as bf
    else:
        import benchmark_functions as bf

    result = bf.scop_gramschmidt(n, m, A, Q, R)
    if return_result:
        return result


def benchmark_lu(dataset, use_optimized_benchmark=False, return_result=False):
    if dataset == MINI_DATA_SET:
        n = 40
    elif dataset == SMALL_DATA_SET:
        n = 120
    elif dataset == LARGE_DATA_SET:
        n = 2000
    elif dataset == EXTRA_LARGE_DATA_SET:
        n = 4000
    else:
        n = 400

    A = __empty_list_2D(n, n)

    for i in range(n):
        for j in range(i + 1):
            A[i][j] = (-j % n) / n + 1
        for j in range(i + 1, n):
            A[i][j] = 0
        A[i][i] = 1

    B = __empty_list_2D(n, n)
    for r in range(n):
        for s in range(n):
            B[r][s] = 0
    for t in range(n):
        for r in range(n):
            for s in range(n):
                B[r][s] += A[r][t] * A[s][t]
        for r in range(n):
            for s in range(n):
                A[r][s] = B[r][s]

    # Function dependency injection
    if use_optimized_benchmark:
        import optimized_benchmark_functions as bf
    else:
        import benchmark_functions as bf

    result = bf.scop_lu(n, A)
    if return_result:
        return result


def benchmark_ludcmp(dataset, use_optimized_benchmark=False, return_result=False):
    if dataset == MINI_DATA_SET:
        n = 40
    elif dataset == SMALL_DATA_SET:
        n = 120
    elif dataset == LARGE_DATA_SET:
        n = 2000
    elif dataset == EXTRA_LARGE_DATA_SET:
        n = 4000
    else:
        n = 400

    A = __empty_list_2D(n, n)
    b = __empty_list_1D(n)
    x = __empty_list_1D(n)
    y = __empty_list_1D(n)

    for i in range(n):
        x[i] = 0
        y[i] = 0
        b[i] = (i + 1) / n / 2.0 + 4
    for i in range(n):
        for j in range(i + 1):
            A[i][j] = (-j % n) / n + 1
        for j in range(i + 1, n):
            A[i][j] = 0
        A[i][i] = 1

    B = __empty_list_2D(n, n)
    for r in range(n):
        for s in range(n):
            B[r][s] = 0
    for t in range(n):
        for r in range(n):
            for s in range(n):
                B[r][s] += A[r][t] * A[s][t]
        for r in range(n):
            for s in range(n):
                A[r][s] = B[r][s]

    # Function dependency injection
    if use_optimized_benchmark:
        import optimized_benchmark_functions as bf
    else:
        import benchmark_functions as bf

    result = bf.scop_ludcmp(n, A, b, x, y)
    if return_result:
        return result


def benchmark_trisolv(dataset, use_optimized_benchmark=False, return_result=False):
    if dataset == MINI_DATA_SET:
        n = 40
    elif dataset == SMALL_DATA_SET:
        n = 120
    elif dataset == LARGE_DATA_SET:
        n = 2000
    elif dataset == EXTRA_LARGE_DATA_SET:
        n = 4000
    else:
        n = 400

    L = __empty_list_2D(n, n)
    x = __empty_list_1D(n)
    b = __empty_list_1D(n)

    for i in range(n):
        x[i] = -999
        b[i] = i
        for j in range(i + 1):
            L[i][j] = (i + n - j + 1) * 2 / n

    # Function dependency injection
    if use_optimized_benchmark:
        import optimized_benchmark_functions as bf
    else:
        import benchmark_functions as bf

    result = bf.scop_trisolv(n, L, x, b)
    if return_result:
        return result


# MEDLEYS

def benchmark_deriche(dataset, use_optimized_benchmark=False, return_result=False):
    if dataset == MINI_DATA_SET:
        w = 64
        h = 64
    elif dataset == SMALL_DATA_SET:
        w = 192
        h = 128
    elif dataset == LARGE_DATA_SET:
        w = 4096
        h = 2160
    elif dataset == EXTRA_LARGE_DATA_SET:
        w = 7680
        h = 4320
    else:
        w = 720
        h = 480

    imgIn = __empty_list_2D(w, h)
    imgOut = __empty_list_2D(w, h)
    y1 = __empty_list_2D(w, h)
    y2 = __empty_list_2D(w, h)
    alpha = 0.25

    for i in range(w):
        for j in range(h):
            imgIn[i][j] = ((313 * i + 991 * j) % 65536) / 65535.0

    k = (1.0 - (e ** (-alpha))) * (1.0 - (e ** -alpha)) / (1.0 + 2.0 * alpha * (e ** (-alpha)) - (e ** (2.0 * alpha)))
    a1 = a5 = k
    a2 = a6 = k * (e ** -alpha) * (alpha - 1.0)
    a3 = a7 = k * (e ** -alpha) * (alpha + 1.0)
    a4 = a8 = -k * (e ** (alpha * 2.0))
    b1 = 2.0 ** (-alpha)
    b2 = -e ** (-2.0 * alpha)
    c1 = c2 = 1

    # Function dependency injection
    if use_optimized_benchmark:
        import optimized_benchmark_functions as bf
    else:
        import benchmark_functions as bf

    result = bf.scop_deriche(w, h, a1, a2, a3, a4, a5, a6, a7, a8, b1, b2, c1, c2, y1, y2, imgIn, imgOut)
    if return_result:
        return result


def benchmark_nussinov(dataset, use_optimized_benchmark=False, return_result=False):
    if dataset == MINI_DATA_SET:
        n = 60
    elif dataset == SMALL_DATA_SET:
        n = 180
    elif dataset == LARGE_DATA_SET:
        n = 2500
    elif dataset == EXTRA_LARGE_DATA_SET:
        n = 5500
    else:
        n = 500

    seq = __empty_list_1D(n)
    table = __empty_list_2D(n, n)

    for i in range(n):
        seq[i] = (i + 1) % 4

    for i in range(n):
        for j in range(n):
            table[i][j] = 0

    # Function dependency injection
    if use_optimized_benchmark:
        import optimized_benchmark_functions as bf
    else:
        import benchmark_functions as bf

    result = bf.scop_nussinov(n, table, seq)
    if return_result:
        return result


# ----------------------------------------------------------------------------------------


# STENCILS

def benchmark_adi(dataset, use_optimized_benchmark=False, return_result=False):
    if dataset == MINI_DATA_SET:
        tsteps = 20
        n = 20
    elif dataset == SMALL_DATA_SET:
        tsteps = 40
        n = 60
    elif dataset == LARGE_DATA_SET:
        tsteps = 500
        n = 1000
    elif dataset == EXTRA_LARGE_DATA_SET:
        tsteps = 1000
        n = 2000
    else:
        tsteps = 100
        n = 200

    u = __empty_list_2D(n, n)
    v = __empty_list_2D(n, n)
    p = __empty_list_2D(n, n)
    q = __empty_list_2D(n, n)
    for i in range(n):
        for j in range(n):
            u[i][j] = (i + n - j) / n

    dx = 1.0 / n
    dy = 1.0 / n
    dt = 1.0 / tsteps
    b1 = 2.0
    b2 = 1.0
    mul1 = b1 * dt / (dx * dx)
    mul2 = b2 * dt / (dy * dy)

    a = -mul1 / 2.0
    b = 1.0 + mul1
    c = a
    d = -mul2 / 2.0
    e = 1.0 + mul2
    f = d

    # Function dependency injection
    if use_optimized_benchmark:
        import optimized_benchmark_functions as bf
    else:
        import benchmark_functions as bf

    result = bf.scop_adi(tsteps, n, u, v, p, q, a, b, c, d, e, f)
    if return_result:
        return result


def benchmark_fdtd_2d(dataset, use_optimized_benchmark=False, return_result=False):
    if dataset == MINI_DATA_SET:
        tmax = 20
        nx = 20
        ny = 30
    elif dataset == SMALL_DATA_SET:
        tmax = 40
        nx = 60
        ny = 80
    elif dataset == LARGE_DATA_SET:
        tmax = 500
        nx = 1000
        ny = 1200
    elif dataset == EXTRA_LARGE_DATA_SET:
        tmax = 1000
        nx = 2000
        ny = 2600
    else:
        tmax = 100
        nx = 200
        ny = 240

    ex = __empty_list_2D(nx, ny)
    ey = __empty_list_2D(nx, ny)
    hz = __empty_list_2D(nx, ny)
    _fict_ = __empty_list_1D(tmax)

    for i in range(tmax):
        _fict_[i] = i
    for i in range(nx):
        for j in range(ny):
            ex[i][j] = (i * (j + 1)) / nx
            ey[i][j] = (i * (j + 2)) / ny
            hz[i][j] = (i * (j + 3)) / nx

    # Function dependency injection
    if use_optimized_benchmark:
        import optimized_benchmark_functions as bf
    else:
        import benchmark_functions as bf

    result = bf.scop_fdtd_2d(tmax, ny, nx, _fict_, hz, ex, ey)
    if return_result:
        return result


def benchmark_head_3d(dataset, use_optimized_benchmark=False, return_result=False):
    if dataset == MINI_DATA_SET:
        tsteps = 20
        n = 10
    elif dataset == SMALL_DATA_SET:
        tsteps = 40
        n = 20
    elif dataset == LARGE_DATA_SET:
        tsteps = 100
        n = 40
    elif dataset == EXTRA_LARGE_DATA_SET:
        tsteps = 500
        n = 120
    else:
        tsteps = 40
        n = 100

    A = __empty_list_3D(n, n, n)
    B = __empty_list_3D(n, n, n)

    for i in range(n):
        for j in range(n):
            for k in range(n):
                A[i][j][k] = B[i][j][k] = (i + j + (n - k)) * 10 / (n)

    # Function dependency injection
    if use_optimized_benchmark:
        import optimized_benchmark_functions as bf
    else:
        import benchmark_functions as bf

    result = bf.scop_head_3d(n, tsteps, A, B)
    if return_result:
        return result


def benchmark_jacobi_1D(dataset, use_optimized_benchmark=False, return_result=False):
    if dataset == MINI_DATA_SET:
        tsteps = 20
        n = 30
    elif dataset == SMALL_DATA_SET:
        tsteps = 40
        n = 120
    elif dataset == LARGE_DATA_SET:
        tsteps = 500
        n = 2000
    elif dataset == EXTRA_LARGE_DATA_SET:
        tsteps = 1000
        n = 4000
    else:
        tsteps = 100
        n = 400

    A = __empty_list_1D(n)
    B = __empty_list_1D(n)

    for i in range(n):
        A[i] = (i + 2) / n
        B[i] = (i + 3) / n

    # Function dependency injection
    if use_optimized_benchmark:
        import optimized_benchmark_functions as bf
    else:
        import benchmark_functions as bf

    result = bf.scop_jacobi_1D(tsteps, n, A, B)
    if return_result:
        return result


def benchmark_jacobi_2D(dataset, use_optimized_benchmark=False, return_result=False):
    if dataset == MINI_DATA_SET:
        tsteps = 20
        n = 30
    elif dataset == SMALL_DATA_SET:
        tsteps = 40
        n = 90
    elif dataset == LARGE_DATA_SET:
        tsteps = 500
        n = 1300
    elif dataset == EXTRA_LARGE_DATA_SET:
        tsteps = 1000
        n = 2800
    else:
        tsteps = 100
        n = 250

    A = __empty_list_2D(n, n)
    B = __empty_list_2D(n, n)

    for i in range(n):
        for j in range(n):
            A[i][j] = (i * (j + 2) + 2) / n
            B[i][j] = (i * (j + 3) + 3) / n

    # Function dependency injection
    if use_optimized_benchmark:
        import optimized_benchmark_functions as bf
    else:
        import benchmark_functions as bf

    result = bf.scop_jacobi_2D(tsteps, n, A, B)
    if return_result:
        return result


def benchmark_seidel_2D(dataset, use_optimized_benchmark=False, return_result=False):
    if dataset == MINI_DATA_SET:
        tsteps = 20
        n = 40
    elif dataset == SMALL_DATA_SET:
        tsteps = 40
        n = 120
    elif dataset == LARGE_DATA_SET:
        tsteps = 500
        n = 2000
    elif dataset == EXTRA_LARGE_DATA_SET:
        tsteps = 1000
        n = 4000
    else:
        tsteps = 100
        n = 400

    A = __empty_list_2D(n, n)

    for i in range(n):
        for j in range(n):
            A[i][j] = (i * (j + 2) + 2) / n

    # Function dependency injection
    if use_optimized_benchmark:
        import optimized_benchmark_functions as bf
    else:
        import benchmark_functions as bf

    result = bf.scop_seidel_2D(tsteps, n, A)
    if return_result:
        return result
