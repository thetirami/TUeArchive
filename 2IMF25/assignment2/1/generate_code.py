def other_remain(exc):
    for i in range(1, 28):
        if i not in exc:
            print('next(C', i, ') = C', i, ' & ', sep='', end='')
    print(';')
    print('TRUE: next(C1) = C1 & next(C2) = C2 & next(C3) = C3 & next(C4) = C4 & next(C5) = C5 & next(C6) = C6 & next(C7) = C7 & next(C8) = C8 & next(C9) = C9 & next(C10) = C10 & next(C11) = C11 & next(C12) = C12 & next(C13) = C13 & next(C14) = C14 & next(C15) = C15 & next(C16) = C16 & next(C17) = C17 & next(C18) = C18 & next(C19) = C19 & next(C20) = C20 & next(C21) = C21 & next(C22) = C22 & next(C23) = C23 & next(C24) = C24 & next(C25) = C25 & next(C26) = C26 & next(C27) = C27; esac |')


def generate(temp):
    info = temp[0]
    channel = temp[1]

    print('case C', channel[0], ' = 0 : next(C', channel[0], ') = ', info, sep='', end=' & ')
    other_remain([channel[0]])

    for i in range(0, len(channel)-1):
        print('case C', channel[i], ' = ', info, ' & C', channel[i+1], ' = 0 : next(C', channel[i], ') = 0 & next(C', channel[i+1], ') = ', info, sep='', end=' & ')
        other_remain([channel[i], channel[i+1]])

    print('case C', channel[-1], ' = ', info, ' : next(C', channel[-1], ') = 0', sep='', end=' & ')
    other_remain([channel[-1]])


todo = [
[12, [11]],
[13, [11, 12]],
[15, [21, 24]],
[11, [12, 13, 14, 23, 22]],
[13, [12]],
[15, [12, 13, 14]],
[11, [13, 14, 23, 22]],
[12, [13, 14, 23, 22, 11]],
[15, [13, 14]],
[11, [23, 22]],
[12, [23, 22, 11]],
[13, [23, 22, 11, 12]]
]

for temp in todo:
    generate(temp)


res = []
for temp in todo:
    info = temp[0]
    channel = temp[1]

    res.append('(C' + str(channel[0]) + ' = 0)')

    for i in range(0, len(channel)-1):
        res.append('(C' + str(channel[i]) + ' = ' + str(info) + ' & C' + str(channel[i+1]) + ' = 0)')

    res.append('(C' + str(channel[-1]) + ' = ' + str(info) + ')')


f_res = []
[f_res.append(i) for i in res if not i in f_res]
for temp in f_res:
    print(temp, sep='', end=' | ')