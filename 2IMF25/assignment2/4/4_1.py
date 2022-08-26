v_num = 6

edge = [
    [1, 2],
    [1, 3],
    [1, 4],
    [1, 5],
    [2, 3],
    [2, 4],
    [2, 5],
    [3, 4],
    [3, 5],
    [4, 5],
    [5, 6]
]

for i in range(1, v_num):
    for j in range(i+1, v_num+1):
        if [i, j] in edge:
            print('(= (e ', i, ' ', j, ') true)', sep='')
        else:
            print('(= (e ', i, ' ', j, ') false)', sep='')

# for i in range(1, v_num):
#     for j in range(i+1, v_num+1):
#         print('(= (e ', i, ' ', j, ') true)', sep='')

# for j in range(1, v_num):
#     for k in range(j+1, v_num+1):
#         print((2*v_num - j)*(j - 1)/2 + (k - j))
