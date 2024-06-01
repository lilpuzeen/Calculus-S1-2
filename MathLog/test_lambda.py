import pytest
from Lambda import TRUE, FALSE, NOT, OR, AND, PEIRCE, SHEFFER, IF, ISZERO, MEDIAN, EVEN, LT, DIV3
from Lambda import ONE, TWO, THREE, FOUR, FIVE, SIX, NINE, ZERO


def church_to_int(church):
	return church(lambda x: x + 1)(0)


@pytest.mark.parametrize('op, expected', [
	(TRUE, FALSE),
	(FALSE, TRUE),
])
def test_not(op, expected):
	assert NOT(op) is expected


@pytest.mark.parametrize('op1, op2, expected', [
	(TRUE, TRUE, TRUE),
	(TRUE, FALSE, TRUE),
	(FALSE, TRUE, TRUE),
	(FALSE, FALSE, FALSE),
])
def test_or(op1, op2, expected):
	assert OR(op1)(op2) is expected


@pytest.mark.parametrize('op1, op2, expected', [
	(TRUE, TRUE, TRUE),
	(TRUE, FALSE, FALSE),
	(FALSE, TRUE, FALSE),
	(FALSE, FALSE, FALSE),
])
def test_and(op1, op2, expected):
	assert AND(op1)(op2) is expected


@pytest.mark.parametrize('op1, op2, expected', [
	(TRUE, TRUE, FALSE),
	(TRUE, FALSE, FALSE),
	(FALSE, TRUE, FALSE),
	(FALSE, FALSE, TRUE),
])
def test_peirce(op1, op2, expected):
	assert PEIRCE(op1)(op2) is expected


@pytest.mark.parametrize('op1, op2, expected', [
	(TRUE, TRUE, FALSE),
	(TRUE, FALSE, TRUE),
	(FALSE, TRUE, TRUE),
	(FALSE, FALSE, TRUE),
])
def test_sheffer(op1, op2, expected):
	assert SHEFFER(op1)(op2) is expected


@pytest.mark.parametrize('op1, op2, op3, expected', [
	(TRUE, TRUE, TRUE, TRUE),
	(TRUE, TRUE, FALSE, TRUE),
	(TRUE, FALSE, TRUE, TRUE),
	(TRUE, FALSE, FALSE, FALSE),
	(FALSE, FALSE, FALSE, FALSE),
])
def test_median(op1, op2, op3, expected):
	assert MEDIAN(op1)(op2)(op3) is expected


@pytest.mark.parametrize('cond, then, else_, expected', [
	(TRUE, TRUE, FALSE, TRUE),
	(TRUE, FALSE, TRUE, FALSE),
	(FALSE, TRUE, FALSE, FALSE),
	(FALSE, FALSE, TRUE, TRUE),
	(TRUE, ONE, TWO, ONE),
	(FALSE, ONE, TWO, TWO),
	(OR(TRUE)(FALSE), ONE, TWO, ONE),
	(AND(TRUE)(FALSE), ONE, TWO, TWO),
])
def test_if(cond, then, else_, expected):
	assert IF(cond)(then)(else_) is expected


@pytest.mark.parametrize('op, expected', [
	(ONE, FALSE),
	(ZERO, TRUE),
])
def test_iszero(op, expected):
	assert ISZERO(op) is expected


@pytest.mark.parametrize('op1, op2, expected', [
	(ONE, TWO, TRUE),
	(TWO, ONE, FALSE),
	(THREE, FOUR, TRUE),
	(FOUR, THREE, FALSE),
	(THREE, THREE, FALSE),
])
def test_lt(op1, op2, expected):
	assert LT(op1)(op2) is expected


@pytest.mark.parametrize('op, expected', [
	(ONE, FALSE),
	(TWO, TRUE),
	(THREE, FALSE),
	(FOUR, TRUE),
])
def test_even(op, expected):
	assert EVEN(op) is expected


@pytest.mark.parametrize('op, expected', [
	(ONE, 1),
	(TWO, 1),
	(THREE, 1),
	# (FOUR, 2),
	# (FIVE, 2),
	# (SIX, 2),
	# (ZERO, 0),
	# (NINE, 3)
])
def test_div3(op, expected):
	assert church_to_int(DIV3(op)) == expected