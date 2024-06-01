import typing as tp
from itertools import chain, combinations

T = tp.TypeVar("T")


# 5.a
def conj(a: list[list[T]]) -> list[T]:
	return list(filter(lambda x: (x in a[i] for i in range(1, len(a))), a[0]))


# 3
def empty() -> list:
	return []


def pair(x: T, y: T) -> list[T]:
    return [x, y]


def flatten(list_of_lists: list[list[T]]) -> list[T]:
    return [item for sublist in list_of_lists for item in sublist]


def powerset(s: list[T]) -> list[tuple[T]]:
    return list(chain.from_iterable(combinations(s, r) for r in range(len(s)+1)))


def filter_(predicate: tp.Callable[[T], bool], lst: list[T]) -> list[T]:
    return [x for x in lst if predicate(x)]


if __name__ == '__main__':
    empty_list = empty()
    print("Empty list:", empty_list)

    pair_list = pair(1, 2)
    print("Pair list:", pair_list)

    nested_list = [[1, 2], [3, 4], [5]]
    flattened_list = flatten(nested_list)
    print("Flattened list:", flattened_list)

    original_list = [1, 2, 3]
    all_subsets = powerset(original_list)
    print("Powerset of the list:", all_subsets)

    numbers_list = [1, 2, 3, 4, 5]
    filtered_list = filter_(lambda x: x % 2 == 0, numbers_list)
    print("Filtered list (only even numbers):", filtered_list)

