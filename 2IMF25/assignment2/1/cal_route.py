rout = [
    [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
    [2, 0, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2],
    [17, 17, 0, 3, 3, 3, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17],
    [26, 26, 26, 0, 4, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26],
    [5, 5, 5, 5, 0, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5],
    [6, 6, 6, 6, 6, 0, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6],
    [19, 19, 19, 19, 19, 19, 0, 7, 7, 7, 19, 19, 19, 19, 19, 19, 19],
    [27, 27, 27, 27, 27, 27, 27, 0, 8, 27, 27, 27, 27, 27, 27, 27, 27],
    [9, 9, 9, 9, 9, 9, 9, 9, 0, 9, 9, 9, 9, 9, 9, 9, 9],
    [10, 10, 10, 10, 10, 10, 10, 10, 10, 0, 10, 10, 10, 10, 10, 10, 10],
    [21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 0, 11, 11, 11, 21, 21, 21],
    [12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 0, 12, 12, 12, 12, 12],
    [13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 0, 13, 13, 13, 13],
    [14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 0, 14, 14, 14],
    [15, 15, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 0, 15, 23],
    [16, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 0, 25],
    [24, 24, 18, 18, 18, 18, 20, 20, 20, 20, 22, 22, 22, 22, 24, 24, 0]
]


def get_dst(channel):
    if channel == 1:
        return 2
    elif channel == 2:
        return 3
    elif channel == 3:
        return 4
    elif channel == 4:
        return 5
    elif channel == 5:
        return 6
    elif channel == 6:
        return 7
    elif channel == 7:
        return 8
    elif channel == 8:
        return 9
    elif channel == 9:
        return 10
    elif channel == 10:
        return 11
    elif channel == 11:
        return 12
    elif channel == 12:
        return 13
    elif channel == 13:
        return 14
    elif channel == 14:
        return 15
    elif channel == 15:
        return 16
    elif channel == 16:
        return 1
    elif channel == 17:
        return 17
    elif channel == 18:
        return 3
    elif channel == 19:
        return 17
    elif channel == 20:
        return 7
    elif channel == 21:
        return 17
    elif channel == 22:
        return 11
    elif channel == 23:
        return 17
    elif channel == 24:
        return 15
    elif channel == 25:
        return 2
    elif channel == 26:
        return 6
    elif channel == 27:
        return 10


def find_route(res, _dep, _dst):
    dep = _dep - 1
    dst = _dst - 1
    if rout[dep][dst] != 0:
        res.append(rout[dep][dst])
        find_route(res, get_dst(rout[dep][dst]), _dst)
    else:
        print('[', _dst, ', ', res, '],', sep='')



m_list = [11, 12, 13, 15]
for i in range(0, len(m_list)):
    for j in range(0, len(m_list)):
        if i != j:
            find_route([], m_list[i], m_list[j])
