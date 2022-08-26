
def print_statement(i, j):
    for k in range(1, 11):
        if k == 2*j-1 or k == 2*j:
            print('\t(= (pos ', i, ' ', k, ') ', j, '))', sep='')


for i in range(1, 6):
    for j in range(1, 6):
        print('(implies (= (dish ', i, ' ', j, ') 1) (and', sep='')
        print_statement(i, j)
        print('))')
