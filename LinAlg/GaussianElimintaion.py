def dot(A, B):
	# Multiply matrix by a matrix
	if type(A[0]) != list:
		A = [A]

	if type(B[0]) != list:
		B = [[b] for b in B]

	ret = [[0] * len(B[0]) for i in range(len(A))]

	for row in range(len(ret)):
		for col in range(len(ret[0])):
			ret[row][col] = 0

			for i in range(len(B)):
				ret[row][col] += A[row][i] * B[i][col]

	# Return scalar if dimensions are 1x1
	if len(ret) == 1 and len(ret[0]) == 1:
		return ret[0][0]
	elif len(ret[0]) == 1:
		# Return vector if dimensions are 1xn
		return [r[0] for r in ret]

	# Return matrix
	return ret


def transpose(A):
    # Calculate matrix transpose
    if type(A[0]) != list:
        A = [A]

    rows = len(A)
    cols = len(A[0])

    B = [[0] * rows for i in range(cols)]

    for row in range(rows):
        for col in range(cols):
            B[col][row] = A[row][col]

    return B


import random

# Number of iterations
iterations = 100

input_matrix = [[4, 1, -2, 2], [1, 2, 0, 1], [-2, 0, 3, -2], [2, 1, -2, -1]]

# Number of eigenvectors and values to recover
N = len(input_matrix[0])

# Eigenvalues
D = [0] * N

for n in range(N):
    # Randomly initialize search vector
    b = [random.random() for i in range(len(input_matrix[0]))]

    dominant_eigenvalue = None
    for k in range(iterations):
        # Input matrix multiplied by b_k
        projection = dot(input_matrix, b)

        # Norm of input matrix multiplied by b_k
        norm = dot(projection, projection) ** 0.5

        # Calculate b_{k+1}
        b_next = [d / norm for d in projection]

        # Calculate the Rayleigh quotient
        dominant_eigenvalue = dot(b, projection) / dot(b, b)

        b = b_next

    D[n] = dominant_eigenvalue

    # Remove current dimensions from the input before moving on
    # the next singular value
    outer_product = [[0] * len(b) for j in range(len(b))]
    for i in range(len(b)):
        for j in range(len(b)):
            outer_product[i][j] = dominant_eigenvalue * b[i] * b[j]

    for i in range(len(input_matrix)):
        for j in range(len(input_matrix[0])):
            input_matrix[i][j] -= outer_product[i][j]


print("Eigenvalues")
print(D)