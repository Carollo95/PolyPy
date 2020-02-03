#!/usr/bin/env python
# -*- coding: utf-8 -*-

from time import time
import benchmarks


LENGTH = 70

NUMBER_OF_ITERATIONS = 100

DATA_SET = benchmarks.STANDARD_DATA_SET
FUNCTIONS = [
    'benchmark_covariance',
    'benchmark_gemm',
    'benchmark_gemerv',
    'benchmark_gesummv',
    'benchmark_symm',
    'benchmark_syr2k',
    'benchmark_syrk',
    'benchmark_trmm',
    'benchmark_2mm',
    'benchmark_3mm',
    'benchmark_atax',
    'benchmark_bicg',
    'benchmark_doitgen',
    'benchmark_mvt',
    'benchmark_cholesky',
    'benchmark_durbin',
    'benchmark_gramschmidt',
    'benchmark_lu',
    'benchmark_ludcmp',
    'benchmark_trisolv',
    'benchmark_deriche',
    'benchmark_nussinov',
    'benchmark_adi',
    'benchmark_fdtd_2d',
    'benchmark_heat_3d',
    'benchmark_jacobi_1D',
    'benchmark_jacobi_2D',
    'benchmark_seidel_2D']

with open('test_results.txt', 'w') as file:
    for function in FUNCTIONS:
        original_benchmark = 'benchmarks.'+function+'(DATA_SET, False, True)'
        optimized_benchmark = 'benchmarks.'+function+'(DATA_SET, True, True)'

        print('#-------------------------------------------------------------------------------------')
        print('#-------------------------------------------------------------------------------------', file=file)
        print('Function:', function)
        print('Function:', function, file=file)
        try:
            if eval(original_benchmark) == eval(optimized_benchmark):
                original_times = []
                optimized_times = []
                for i in range(NUMBER_OF_ITERATIONS):
                    percentage = int(i / NUMBER_OF_ITERATIONS * LENGTH)
                    print('\r' + '#' * percentage + '_' * (LENGTH - percentage) +
                          ' {:5.2f}% completed'.format(i / NUMBER_OF_ITERATIONS * 100), end='')
                    before = time()
                    eval(original_benchmark)
                    after = time()
                    original_times.append(after-before)

                    before = time()
                    eval(optimized_benchmark)
                    after = time()
                    optimized_times.append(after-before)

                mean_original_time = sum(original_times) / len(original_times)
                mean_optimized_time = sum(optimized_times) / len(optimized_times)
                print('\rNumber of iterations of algorithm: {}                                                '
                      .format(NUMBER_OF_ITERATIONS))
                print('Number of iterations of algorithm: {}                                                '
                      .format(NUMBER_OF_ITERATIONS), file=file)
                print('Mean original time: {}'.format(mean_original_time))
                print('Mean original time: {}'.format(mean_original_time), file=file)
                print('Mean optimized time: {}'.format(mean_optimized_time))
                print('Mean optimized time: {}'.format(mean_optimized_time),file=file)
                improvement = (mean_optimized_time - mean_original_time) / mean_original_time * -100
                if improvement > 0:
                    print('\033[32m' + 'Improvement: {:2f}%'.format(improvement) + '\033[0m' + '\n')
                else:
                    print('\033[31m' + 'Improvement: {:2f}%'.format(improvement) + '\033[0m' + '\n')
                print('Improvement: {:2f}%\n'.format(improvement), file=file)

            else:
                raise Exception
        except Exception:
            print('\033[93m' + 'Functions won\'t yield the same results' + '\033[0m' + '\n')
            print('Functions won\'t yield the same results\n', file=file)
