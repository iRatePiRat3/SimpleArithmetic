from fractions import Fraction

def trailing_ones_length(n):
    """Compute ℓ(n) = number of trailing 1s in binary representation"""
    if n == 0:
        return 0
    count = 0
    while n & 1:
        count += 1
        n >>= 1
    return count

def v2(n):
    """Compute v_2(n) = highest power of 2 dividing n"""
    if n == 0:
        return 0
    count = 0
    while n % 2 == 0:
        count += 1
        n //= 2
    return count

def collatz_step_box_tracking(n):
    """Track the Collatz step using actual box counting"""
    if n % 2 == 0:
        raise ValueError("Input must be odd")
    
    l_n = trailing_ones_length(n)
    B = 2 ** l_n
    
    # Decompose n into full boxes and fractional part
    full_boxes = Fraction(n // B)
    fractional_units = Fraction(n % B)
    
    step_data = {
        'n': n,
        'l': l_n,
        'B': B,
        'full_boxes': full_boxes,
        'fractional_units': fractional_units,
    }
    
    # TRIPLING
    new_full_boxes = 3 * full_boxes
    new_fractional_units = 3 * fractional_units
    
    step_data['after_triple_full'] = new_full_boxes
    step_data['after_triple_frac'] = new_fractional_units
    
    # ADD 1
    new_fractional_units += 1
    
    step_data['after_add_one_frac'] = new_fractional_units
    
    # Determine v_2(3n + 1)
    three_n_plus_1 = 3 * n + 1
    v2_value = v2(three_n_plus_1)
    
    step_data['v2_of_3n_plus_1'] = v2_value
    
    # DIVISION BY 2^v2_value
    for _ in range(v2_value):
        new_full_boxes = new_full_boxes / 2
        new_fractional_units = new_fractional_units / 2
    
    step_data['after_division_full'] = new_full_boxes
    step_data['after_division_frac'] = new_fractional_units
    
    # Compute next n
    n_next = int(new_full_boxes * B + new_fractional_units)
    
    step_data['n_next'] = n_next
    
    # Compute new decomposition
    l_next = trailing_ones_length(n_next)
    B_next = 2 ** l_next
    full_boxes_next = Fraction(n_next // B_next)
    fractional_units_next = Fraction(n_next % B_next)
    
    step_data['l_next'] = l_next
    step_data['B_next'] = B_next
    step_data['full_boxes_next'] = full_boxes_next
    step_data['fractional_units_next'] = fractional_units_next
    
    return step_data

def print_step(step_data, step_num=0):
    """Pretty-print a single step"""
    print(f"\n{'─'*100}")
    print(f"STEP {step_num}: n = {step_data['n']}")
    print(f"{'─'*100}")
    print(f"\nInitial Decomposition (ℓ = {step_data['l']}, B = {step_data['B']}):")
    print(f"  {step_data['full_boxes']} full boxes + {step_data['fractional_units']} units in partial box")
    print(f"  = {step_data['full_boxes']} × {step_data['B']} + {step_data['fractional_units']}")
    
    print(f"\nAfter Tripling (×3):")
    print(f"  Full boxes: {step_data['after_triple_full']}")
    print(f"  Fractional units: {step_data['after_triple_frac']}")
    
    print(f"\nAfter Adding 1:")
    print(f"  Full boxes: {step_data['after_triple_full']}")
    print(f"  Fractional units: {step_data['after_add_one_frac']}")
    
    print(f"\nDivision Phase (÷ 2^{step_data['v2_of_3n_plus_1']}):")
    print(f"  Full boxes after division: {step_data['after_division_full']}")
    print(f"  Fractional units after division: {step_data['after_division_frac']}")
    
    print(f"\nNext Value n' = {step_data['n_next']}")
    print(f"Next Decomposition (ℓ = {step_data['l_next']}, B = {step_data['B_next']}):")
    print(f"  {step_data['full_boxes_next']} full boxes + {step_data['fractional_units_next']} units")

# Detailed trace for n = 31
print("\n" + "="*100)
print("DETAILED TRACE: n = 31 (AS YOUR EXAMPLE)")
print("="*100)

current = 31
for step_num in range(8):
    if current == 1:
        print("\n✓ Reached 1")
        break
    step_data = collatz_step_box_tracking(current)
    print_step(step_data, step_num)
    current = step_data['n_next']

# Trajectory summary for multiple values
print("\n\n" + "="*100)
print("TRAJECTORY ANALYSIS")
print("="*100)

for n_start in [31, 27, 231, 3077]:
    print(f"\n{'='*100}")
    print(f"n = {n_start}")
    print(f"{'='*100}")
    
    trajectory = []
    current = n_start
    step_count = 0
    
    while current != 1 and step_count < 100000:
        step_data = collatz_step_box_tracking(current)
        trajectory.append(step_data)
        current = step_data['n_next']
        step_count += 1
    
    print(f"Steps to convergence: {len(trajectory)}")
    
    if trajectory:
        # Analyze fractional accumulation
        frac_ratios = []
        for step in trajectory:
            if step['B'] > 0:
                frac_ratio = float(step['fractional_units']) / step['B']
                frac_ratios.append(frac_ratio)
        
        print(f"\nFractional Box Content Statistics:")
        print(f"  Mean fractional content: {sum(frac_ratios)/len(frac_ratios):.6f}")
        print(f"  Max fractional content:  {max(frac_ratios):.6f}")
        print(f"  Min fractional content:  {min(frac_ratios):.6f}")
        
        # Box level dynamics
        box_ups = sum(1 for s in trajectory if s['l_next'] > s['l'])
        box_downs = sum(1 for s in trajectory if s['l_next'] < s['l'])
        box_same = sum(1 for s in trajectory if s['l_next'] == s['l'])
        
        print(f"\nBox Level Transitions:")
        print(f"  Level increases (ℓ ↑): {box_ups}")
        print(f"  Level decreases (ℓ ↓): {box_downs}")
        print(f"  Level stable (ℓ =):    {box_same}")
        
        # Overflow tracking
        overflow_count = 0
        for step in trajectory:
            if step['after_add_one_frac'] > step['B']:
                overflow_count += 1
        
        print(f"\nOverflow Events (fractional > box size):")
        print(f"  Count: {overflow_count} / {len(trajectory)}")
        
        print(f"\nFirst 15 steps:")
        print(f"{'Step':>4} | {'n':>6} | {'ℓ':>2} | {'Full':>4} | {'Frac':>6} | {'After÷2 Full':>12} | {'After÷2 Frac':>12} | {'n'':>6} | {'ℓ'':>2}")
        print("-" * 120)
        for i, step in enumerate(trajectory[:15]):
            print(f"{i:>4} | {step['n']:>6} | {step['l']:>2} | {float(step['full_boxes']):>4.1f} | {float(step['fractional_units']):>6.2f} | "
                  f"{float(step['after_division_full']):>12.2f} | {float(step['after_division_frac']):>12.4f} | {step['n_next']:>6} | {step['l_next']:>2}")
