import numpy as np
from numpy.typing import NDArray


def mult(A: NDArray, B: NDArray):
    # A - row, B - matrix (2,0)
    C_ilt = np.array([[[10, -2, -6], [-5, 1, 3], [10, -2, -6]], [[10, -10, -10], [-5, 5, 5], [10, -10, -10]], [[-2, -2, -4], [1, 1, 2], [-2, -2, -4]]])
    result = np.zeros_like(C_ilt)
    for k in range(3):
        for i in range(3):
            for j in range(3):
                result[k][i][j] = A[i] * B[j][k]
    return result


print(mult(np.array([-2, 1, -2]), np.array([[-5, -5, 1], [1, 5, 1], [3, 5, 2]])))
