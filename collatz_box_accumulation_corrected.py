def collatz(n):
    sequence = [n]
    while n != 1:
        if n % 2 == 0:
            n //= 2
        else:
            n = 3 * n + 1
        sequence.append(n)
    return sequence

if __name__ == '__main__':
    n = int(input('Enter a positive integer: '))
    print(collatz(n))