def DEBUG(string, color = "35"):
    print("\033[+" + color + "+m{}\033[00m" .format(string))

# this is a helper function
def add(list, exp, n):
    if n == 1:
        exp = list[0]
        return exp

    exp = list[n - 1] + list[n - 2]
    list[n - 2] = exp
    return add(list, exp, n-1)