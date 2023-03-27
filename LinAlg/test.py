import random
from functools import lru_cache

import numpy as np
import scipy.linalg as sp
from Stringify import to_string

a_cos = np.array([[-4, 1, 0, 0, 0],
                  [13, 1, 4, 2, 1],
                  [-47, -24, -17, -7, -4],
                  [33, 16, 8, 1, 3],
                  [17, 8, 4, 2, -2]])
