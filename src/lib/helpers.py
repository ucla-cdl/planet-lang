def DEBUG(string, color = "35"):
    print("\033[+" + color + "+m{}\033[00m" .format(string))