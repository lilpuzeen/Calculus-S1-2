def to_string(a):
	result = ""
	for i in range(len(a)):
		for j in range(len(a[i])):
			if j != len(a) - 1:
				result += str(a[i][j]) + ", "
			else:
				result += str(a[i][j]) + "; "
	return "[" + result[:-2] + "]"
