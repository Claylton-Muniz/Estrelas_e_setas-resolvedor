from z3 import *

n = 5  # tamanho do tabuleiro (N x N)

# Regras
pecas = []
lin = []
col = []
seta_dir = []
seta_esq = []
seta_cim = []
seta_bai = []
seta_dse = []  # diagonal superior esquerda
seta_dsd = []  # diagonal superior direita
seta_die = []  # diagonal inferior esquerda
seta_did = []  # diagonal inferior direita
not_setas = []

# Valores para testar soluções
# start_tab = [[8, 0, 6],
#              [5, 0, 0],
#              [0, 0, 0]]
# start_tab_l = [0,
#                2,
#                2]
# start_tab_c = [1, 1, 2]
start_tab = []
start_tab_l = []
start_tab_c = []
start_position = []
start_position_lc = []

# Variáveis inteiras do tabuleiro N x N
tab = [[Int(f'x_{i}_{j}') for j in range(n)] for i in range(n)]

# Quantidade de estrelas por linha e coluna
lin_quant = [Int(f'row_{i}') for i in range(n)]
col_quant = [Int(f'col_{i}') for i in range(n)]

solver = Solver()

# Restrição peças
# -----------------------------------------------------------------------------
#   1  2  3
#   ↖  ↑  ↗
# 4 ←     → 5 - As direções são representadas por números da seguinte forma.
#   ↙  ↓  ↘
#   6  7  8
#
#   0 -> vazio
#   9 -> estrela
# -----------------------------------------------------------------------------
for i in range(n):
    for j in range(n):
        pecas.append(And(0 <= tab[i][j], tab[i][j] <= 9))
solver.add(pecas)

# Restrição setas
for i in range(n):
    for j in range(n):
        seta_dir.append(Implies(tab[i][j] == 5, And([Or(And(tab[i][k] > 0, tab[i][k] < 9), tab[i][k] == 0,
                                                        tab[i][k] == 9) for k in range(j + 1, n)])))
        seta_esq.append(
            Implies(tab[i][j] == 4, And([Or(And(tab[i][k] > 0, tab[i][k] < 9), tab[i][k] == 0,
                                            tab[i][k] == 9) for k in range(j - 1, -1, -1)])))
        seta_cim.append(
            Implies(tab[i][j] == 2, And([Or(And(tab[k][j] > 0, tab[k][j] < 9), tab[k][j] == 0,
                                            tab[k][j] == 9) for k in range(i - 1, -1, -1)])))
        seta_bai.append(Implies(tab[i][j] == 7, And([Or(And(tab[k][j] > 0, tab[k][j] < 9), tab[k][j] == 0,
                                                        tab[k][j] == 9) for k in range(i + 1, n)])))
        seta_dse.append(Implies(tab[i][j] == 1,
                                And([Or(And(tab[k][r] > 0, tab[k][r] < 9),
                                        tab[k][r] == 0, tab[k][r] == 9) for k in range(i - 1, -1, -1)
                                     for r in range(j - 1, -1, -1) if k - r == i - j])))
        seta_dsd.append(Implies(tab[i][j] == 3,
                                And([Or(And(tab[k][r] > 0, tab[k][r] < 9),
                                        tab[k][r] == 0, tab[k][r] == 9) for k in range(i - 1, -1, -1)
                                     for r in range(j + 1, n) if k + r == i + j])))
        seta_die.append(Implies(tab[i][j] == 6,
                                And([Or(And(tab[k][r] > 0, tab[k][r] < 9),
                                        tab[k][r] == 0, tab[k][r] == 9) for k in range(i + 1, n)
                                     for r in range(j - 1, -1, -1) if k + r == i + j])))
        seta_did.append(Implies(tab[i][j] == 8,
                                And([Or(And(tab[k][r] > 0, tab[k][r] < 9),
                                        tab[k][r] == 0, tab[k][r] == 9) for k in range(i + 1, n)
                                     for r in range(j + 1, n) if k - r == i - j])))

setas = seta_dir + seta_esq + seta_cim + seta_bai + seta_dse + seta_dsd + seta_die + seta_did
solver.add(setas)

# Restrições de estrelas - linha e coluna
for i in range(n):
    solver.add(Sum([If(tab[i][j] == 9, 1, 0) for j in range(n)]) == lin_quant[i])
    solver.add(Sum([If(tab[j][i] == 9, 1, 0) for j in range(n)]) == col_quant[i])

for i in range(n):
    start_tab_l.append(int(input(f'lin_{i}: ')))

for i in range(n):
    start_tab_c.append(int(input(f'col_{i}: ')))

for i in range(n):
    linha = []
    for j in range(n):
        linha.append(int(input(f'x_{i}_{j}: ')))
    start_tab.append(linha)

for i in range(n):
    for j in range(n):
        not_setas.append(If(And(start_tab[i][j] > 0, start_tab[i][j] < 9), And(tab[i][j] > 0, tab[i][j] < 9),
                            Or(tab[i][j] == 0, tab[i][j] == 9)))
    solver.add(not_setas)

for i in range(n):
    start_position_lc.append(And(start_tab_l[i] == lin_quant[i],
                                 start_tab_c[i] == col_quant[i]))
solver.add(start_position_lc)

for i in range(n):
    for j in range(n):
        start_position.append(If(start_tab[i][j] == 0, True, tab[i][j] == start_tab[i][j]))
solver.add(start_position)

if solver.check() == sat:
    solver.add()
    print('sat')
    solution = solver.model()
    ret_val = []
    for i in range(n):
        linha = []
        ret_val.append(linha)
        for j in range(n):
            ret_val[i].append(solution.evaluate(tab[i][j]))
    for i in range(n):
        for j in range(n):
            if ret_val[i][j] == 0:
                print('[ ]', end='')
            elif ret_val[i][j] == 1:
                print('[↖]', end='')
            elif ret_val[i][j] == 2:
                print('[↑]', end='')
            elif ret_val[i][j] == 3:
                print('[↗]', end='')
            elif ret_val[i][j] == 4:
                print('[←]', end='')
            elif ret_val[i][j] == 5:
                print('[→]', end='')
            elif ret_val[i][j] == 6:
                print('[↙]', end='')
            elif ret_val[i][j] == 7:
                print('[↓]', end='')
            elif ret_val[i][j] == 8:
                print('[↘]', end='')
            elif ret_val[i][j] == 9:
                print('[*]', end='')
        print()

else:
    print('Não há solução.')
