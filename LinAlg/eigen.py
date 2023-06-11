import numpy as np
import scipy.linalg as sp
from Stringify import to_string
A = np.array([[5, 2, -1, 0, 0], [0, 4, 1, 0, 0], [0, -1, 7, 1, 0], [0, 1, -2, 4, 0], [0, -1, 1, 0, 5]])

print(to_string(2*A + 0.5 * sp.expm(A * 0.5)))

# print(mult(np.array([-2, 1, -2]), np.array([[-5, -5, 1], [1, 5, 1], [3, 5, 2]])))
