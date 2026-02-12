# Collatz Box Accumulation

def collatz(n):
    steps = 0
    while n != 1:
        if n % 2 == 0:
            n //= 2
        else:
            n = 3 * n + 1
        steps += 1
    return steps

if __name__ == '__main__':
    number = int(input('Enter a number: '))
    print(f'The Collatz sequence takes {collatz(number)} steps to reach 1.')