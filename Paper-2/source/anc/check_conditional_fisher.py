"""Exact checks of the finite tilted-chain example; no Yang--Mills simulation."""
from fractions import Fraction as F
from itertools import product


def main():
    n = 2
    m, delta, theta = n ** 3, F(1, n ** 3), F(1, n)
    states = list(product([0, 1], range(m)))
    pi = [((1 - delta) if j == 0 else delta) / m for j, _ in states]
    count = len(states)
    projection = [[F(0) for _ in states] for _ in states]
    for i, (jx, kx) in enumerate(states):
        for j, (jy, ky) in enumerate(states):
            if jx == 0 and jy == 0:
                projection[i][j] = F(1, m)
            elif jx == 1 and jy == 1 and kx == ky:
                projection[i][j] = F(1)
    transition = [[theta * projection[i][j] + (1 - theta) * pi[j]
                   for j in range(count)] for i in range(count)]
    for i in range(count):
        assert sum(projection[i]) == sum(transition[i]) == 1
        for j in range(count):
            assert transition[i][j] > 0
            assert pi[i] * transition[i][j] == pi[j] * transition[j][i]
            assert sum(projection[i][k] * projection[k][j] for k in range(count)) == projection[i][j]
    trace_square = sum(transition[i][j] * transition[j][i]
                       for i in range(count) for j in range(count))
    assert trace_square == 1 + m * theta ** 2 == 1 + n
    # Compute the likelihood and both chi-square expectations directly,
    # rather than assuming the formulas in the note.
    s1 = bare_second = weighted_second_numerator = F(0)
    for i, (jx, kx) in enumerate(states):
        for jy, group_mass in [(0, 1 - delta), (1, delta)]:
            indices = [j for j, (jgroup, _) in enumerate(states) if jgroup == jy]
            reached_mass = sum(transition[i][j] for j in indices)
            first = reached_mass / group_mass
            chi = sum(F(1, m) * ((transition[i][j] / reached_mass) * m - 1) ** 2
                      for j in indices)
            history_mass = pi[i] * group_mass
            s1 += history_mass * first ** 2
            bare_second += history_mass * chi
            weighted_second_numerator += history_mass * first ** 2 * chi
    c = theta / (theta + (1 - theta) * delta)
    assert s1 == 1 + theta ** 2
    assert bare_second == delta ** 2 * c ** 2 * (m - 1)
    tilted_second = weighted_second_numerator / s1
    assert tilted_second == theta ** 2 * (m - 1) / (1 + theta ** 2)
    assert s1 * (1 + tilted_second) == trace_square
    for n in range(2, 31):
        m, delta, theta = n ** 3, F(1, n ** 3), F(1, n)
        c = theta / (theta + (1 - theta) * delta)
        assert delta ** 2 * c ** 2 * (m - 1) < F(1, n ** 3)
        assert theta ** 2 * (m - 1) / (1 + theta ** 2) == F(n ** 3 - 1, n ** 2 + 1)
    assert F(1, 8195) / (1 - F(1, 8195)) == F(1, 8194)
    # The product-versus-sum bound used in the Fisher-budget theorem.
    eta = [F(1, 100000), F(2, 100000), F(3, 100000)]
    product_budget = F(1)
    for value in eta:
        product_budget *= 1 - value
    assert product_budget >= 1 - sum(eta)
    print("Passed exact projection, reversibility, likelihood-chain and rational-budget checks.")
    print("These finite checks do not establish the tuned Wilson score bound.")


if __name__ == "__main__":
    main()
