def other_remain(exc):
    for i in range(1, 28):
        if i not in exc:
            print('next(C', i, ') = C', i, ' & ', sep='', end='')
    print(';')
    print('TRUE: next(C1) = C1 & next(C2) = C2 & next(C3) = C3 & next(C4) = C4 & next(C5) = C5 & next(C6) = C6 & next(C7) = C7 & next(C8) = C8 & next(C9) = C9 & next(C10) = C10 & next(C11) = C11 & next(C12) = C12 & next(C13) = C13 & next(C14) = C14 & next(C15) = C15 & next(C16) = C16 & next(C17) = C17 & next(C18) = C18 & next(C19) = C19 & next(C20) = C20 & next(C21) = C21 & next(C22) = C22 & next(C23) = C23 & next(C24) = C24 & next(C25) = C25 & next(C26) = C26 & next(C27) = C27; esac |')

def the_other(channel):
    if channel == 17:
        return 18
    elif channel == 18:
        return 17
    elif channel == 19:
        return 20
    elif channel == 20:
        return 19
    elif channel == 21:
        return 22
    elif channel == 22:
        return 21
    elif channel == 23:
        return 24
    elif channel == 24:
        return 23


def generate(temp):
    info = temp[0]
    channel = temp[1]

    if channel[0] in [17, 18, 19, 20, 21, 22, 23, 24]:
        print('case C', channel[0], ' = 0 : next(C', channel[0], ') = ', info, ' & next(C', the_other(channel[0]), ') = ', info, sep='', end=' & ')
        other_remain([channel[0], the_other(channel[0])])
    else:
        print('case C', channel[0], ' = 0 : next(C', channel[0], ') = ', info, sep='', end=' & ')
        other_remain([channel[0]])

    for i in range(0, len(channel)-1):
        if channel[i] in [17, 18, 19, 20, 21, 22, 23, 24] and channel[i+1] in [17, 18, 19, 20, 21, 22, 23, 24]:
            print('case C', channel[i], ' = ', info, ' & C', channel[i+1], ' = 0 : next(C', channel[i], ') = 0 & next(C', the_other(channel[i]), ') = 0 & next(C', channel[i+1], ') = ', info, ' & next(C', the_other(channel[i+1]), ') = ', info, sep='', end=' & ')
            other_remain([channel[i], channel[i+1], the_other(channel[i]), the_other(channel[i+1])])
        elif channel[i] in [17, 18, 19, 20, 21, 22, 23, 24] and channel[i+1] not in [17, 18, 19, 20, 21, 22, 23, 24]:
            print('case C', channel[i], ' = ', info, ' & C', channel[i+1], ' = 0 : next(C', channel[i], ') = 0 & next(C', the_other(channel[i]), ') = 0 & next(C', channel[i+1], ') = ', info, sep='', end=' & ')
            other_remain([channel[i], channel[i+1], the_other(channel[i])])
        elif channel[i] not in [17, 18, 19, 20, 21, 22, 23, 24] and channel[i+1] in [17, 18, 19, 20, 21, 22, 23, 24]:
            print('case C', channel[i], ' = ', info, ' & C', channel[i+1], ' = 0 : next(C', channel[i], ') = 0 & next(C', channel[i+1], ') = ', info, ' & next(C', the_other(channel[i+1]), ') = ', info, sep='', end=' & ')
            other_remain([channel[i], channel[i+1], the_other(channel[i+1])])
        else:
            print('case C', channel[i], ' = ', info, ' & C', channel[i+1], ' = 0 : next(C', channel[i], ') = 0 & next(C', channel[i+1], ') = ', info, sep='', end=' & ')
            other_remain([channel[i], channel[i+1]])

    if channel[-1] in [17, 18, 19, 20, 21, 22, 23, 24]:
        print('case C', channel[-1], ' = ', info, ' : next(C', channel[-1], ') = 0 & next(C', the_other(channel[-1]), ') = 0', sep='', end=' & ')
        other_remain([channel[-1], the_other(channel[-1])])
    else:
        print('case C', channel[-1], ' = ', info, ' : next(C', channel[-1], ') = 0', sep='', end=' & ')
        other_remain([channel[-1]])


todo = [
    [11, [5, 6, 19, 22]],
    [14, [5, 6, 19, 22, 11, 12, 13]],
    [5, [21, 18, 3, 4]],
    [14, [11, 12, 13]],
    [5, [14, 23, 18, 3, 4]],
    [11, [14, 23, 22]]
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