v_num = 20

edge = [
    [1, 2],
    [1, 5],
    [1, 6],
    [2, 3],
    [2, 8],
    [3, 4],
    [3, 10],
    [4, 5],
    [4, 12],
    [5, 14],
    [6, 7],
    [6, 15],
    [7, 8],
    [7, 16],
    [8, 9],
    [9, 10],
    [9, 17],
    [10, 11],
    [11, 12],
    [11, 18],
    [12, 13],
    [13, 14],
    [13, 19],
    [14, 15],
    [15, 20],
    [16, 17],
    [16, 20],
    [17, 18],
    [18, 19],
    [19, 20]
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
