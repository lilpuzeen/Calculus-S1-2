IDENTITY = lambda x: x

TRUE = lambda x: lambda y: x
FALSE = lambda x: lambda y: y

NOT = lambda cond: cond(FALSE)(TRUE)
OR  = lambda a: lambda b: a(TRUE)(b)
AND = lambda a: lambda b: a(b)(FALSE)
PEIRCE = lambda a: lambda b: NOT(OR(a)(b))
SHEFFER = lambda a: lambda b: NOT(AND(a)(b))
MEDIAN = lambda a: lambda b: lambda c: AND(OR(a)(b))(AND(OR(b)(c))(OR(a)(c)))

# COMBINATORS REGION
I = IDENTITY
K = TRUE
S = lambda a: lambda b: lambda c: a(c)(b(c))
Y = lambda f: (
    (lambda x: f(lambda y: x(x)(y)))
    (lambda x: f(lambda y: x(x)(y)))
)
# END REGION

ZERO = lambda f: lambda x: x
ONE = lambda f: lambda x: f(x)
TWO = lambda f: lambda x: f(f(x))
THREE = lambda f: lambda x: f(f(f(x)))
FOUR = lambda f: lambda x: f(f(f(f(x))))
FIVE = lambda f: lambda x: f(f(f(f(f(x)))))
SIX = lambda f: lambda x: f(f(f(f(f(f(x))))))
NINE = lambda f: lambda x: f(f(f(f(f(f(f(f(f(x)))))))))

IF = lambda cond: lambda then: lambda else_: cond(then)(else_)
ISZERO = lambda a: a(lambda _: FALSE)(TRUE)

INC = lambda n: lambda f: lambda x: f(n(f)(x))
DEC = lambda n: lambda f: lambda x: n(lambda g: lambda h: h(g(f)))(lambda u: x)(lambda u: u)
SUB = lambda m: lambda n: n(DEC)(m)

LTE = lambda a: lambda b: ISZERO(SUB(a)(b))
LT  = lambda a: lambda b: LTE(a)(DEC(b))
EQ = lambda a: lambda b: AND(ISZERO(SUB(a)(b)))(ISZERO(SUB(b)(a)))

EVEN = lambda a: a(NOT)(TRUE)

MOD = Y(
    lambda f: lambda a: lambda b: LT(a)(b)
    (lambda _: a)
    (lambda _: f(SUB(a)(b))(b))
    (ZERO)
)


DIV = Y(
    lambda f: lambda a: lambda b: LT(a)(b)
    (lambda _: ZERO)
    (lambda _: INC(f(SUB(a)(b))(b)))
    (ZERO)
)
# DIV = Y(
#     lambda f: lambda a: lambda b: LT(a)(b)
#     (lambda _: ZERO)
#     (lambda _: IF(ISZERO(MOD(a)(b)))
#                  (lambda: f(SUB(a)(b))(b))
#                  (lambda: INC(f(SUB(a)(b))(b)))
#     )
# )


DIV3 = lambda x: DIV(x)(THREE)

# numerator = FOUR
# denominator = TWO
# result = div(numerator)(denominator)
# result_div3 = div3(TWO)
# print(church_to_int(result))
# print(church_to_int(result_div3))