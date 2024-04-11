def to_string(a):
	result = ""
	for i in range(len(a)):
		for j in range(len(a[i])):
			if j != len(a) - 1:
				result += str(a[i][j]) + ", "
			else:
				result += str(a[i][j]) + "; "
	return "[" + result[:-2] + "]"

import numpy as np

G = np.array([[13, 34, 31], [34, 89, 81], [31, 81, 74]])
print(np.linalg.det(G))

import numpy as np

def scalar_product(x, G, y):
    return x.transpose() @ G @ y


def proj(a, b, G):
    return scalar_product(a, G, b) / scalar_product(b, G, b) * b

def norm(a, G):
    return scalar_product(a, G, a) ** 0.5

x = np.array([-2, 1, 3])

G = np.array([[2, -3, 1], [-3, 6, -1], [1, -1, 1]])

y = np.array([[4, 1], [-2, 0], [-5, -1]])

normX = np.sqrt(scalar_product(x, G, x))
normY = np.sqrt(scalar_product(y, G, y))


scalar = scalar_product(x, G, y)

cos = (scalar[0][0] / (normX[0][0] * normY[0][0]))

print(np.arccos(cos))