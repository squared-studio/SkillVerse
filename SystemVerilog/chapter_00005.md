# Array Manipulation

## Introduction
SystemVerilog provides powerful array manipulation methods that enable efficient data processing in verification and RTL design. These methods operate on **dynamic arrays**, **queues**, and **associative arrays**, offering functionality similar to modern programming languages while maintaining hardware-centric optimizations.

## Array Methods Overview

### Searching & Filtering Methods
| Method                 | Description                                                                 | Example with Expression                  |
|------------------------|-----------------------------------------------------------------------------|------------------------------------------|
| **`find()`**           | Returns all elements matching the condition                                | `array.find(x) with (x > 5)`             |
| **`find_index()`**     | Returns indices of matching elements                                       | `array.find_index(x) with (x % 2 == 0)`  |
| **`find_first()`**     | Returns first matching element                                             | `array.find_first(x) with (x < 0)`       |
| **`find_last()`**      | Returns last matching element                                              | `array.find_last(x) with (x == 255)`     |
| **`unique()`**         | Returns unique element values                                              | `array.unique()`                         |
| **`unique_index()`**   | Returns indices of first occurrence of unique values                       | `array.unique_index()`                   |

### Sorting & Ordering Methods
| Method                 | Description                                                                 | Example with Custom Sort                |
|------------------------|-----------------------------------------------------------------------------|------------------------------------------|
| **`sort()`**           | Sorts elements in ascending order (modifies original array)                | `array.sort() with (x < y)`             |
| **`rsort()`**          | Sorts elements in descending order                                         | `array.rsort() with (item > item)`      |
| **`reverse()`**        | Reverses element order in-place                                            | `array.reverse()`                       |
| **`shuffle()`**        | Randomizes element order                                                   | `array.shuffle()`                       |

### Mathematical Operations
| Method                 | Description                                                                 | Note                                     |
|------------------------|-----------------------------------------------------------------------------|------------------------------------------|
| **`sum()`**            | Returns sum of all elements                                                 | Auto-casts to array type                 |
| **`product()`**        | Returns product of all elements                                            | Watch for integer overflow               |
| **`min()`**            | Returns smallest element value                                             | Works with `with` clauses                |
| **`max()`**            | Returns largest element value                                              | Supports complex expressions             |

### Bitwise Operations
| Method                 | Description                                                                 | Typical Use Case                        |
|------------------------|-----------------------------------------------------------------------------|------------------------------------------|
| **`and()`**            | Bitwise AND of all elements                                                 | `array.and()` → `&array[0] & array[1]...`|
| **`or()`**             | Bitwise OR of all elements                                                  | Flag combination checks                  |
| **`xor()`**            | Bitwise XOR of all elements                                                 | Parity calculation                       |

## Enhanced Examples with Outputs

### 1. Advanced Filtering with `find()`
```SV
int temperatures[] = {-5, 12, 23, -3, 42, 18};
int below_zero[] = temperatures.find(x) with (x < 0);
// Result: below_zero = '{-5, -3}
```

### 2. Custom Sorting with `with` Clause
```SV
string names[] = {"Alice", "Bob", "Charlie"};
names.sort(x) with (x.len());  // Sort by string length
// Result: {"Bob", "Alice", "Charlie"}
```

### 3. Bitwise Operations with Packed Arrays
```SV
bit [3:0] masks[] = {4'b1010, 4'b1100, 4'b1111};
bit [3:0] combined_and = masks.and();
// Result: combined_and = 4'b1000 (1010 & 1100 & 1111)
```

### 4. Complex `unique_index()` Usage
```SV
int data[] = {5, 2, 5, 7, 2, 9};
int first_unique_indices[] = data.unique_index();
// Result: indices = {0, 1, 3, 5} (first occurrences of 5,2,7,9)
```

### 5. Multi-method Chaining
```SV
int values[] = {8, 3, 5, 8, 2, 5};
int result = values.unique().sum();  // Unique values: {8,3,5,2} → Sum=18
```

## Key Considerations
1. **Modification Warnings**: Methods like `sort()`, `reverse()`, and `shuffle()` modify the original array
2. **`with` Clause Flexibility**: Most methods accept complex expressions:
   ```SV
   struct {int age; string name;} people[];
   people.sort(x) with (x.age);  // Sort structs by age
   ```
3. **Null Handling**: Methods return empty arrays when no matches found
4. **Performance**: Associative array methods (`unique`, `sort`) have O(n log n) complexity

## Practical Exercises
1. **Data Validation**: Find all transactions with amounts > $1000 in a queue of financial records
2. **Packet Processing**: Calculate checksum (XOR) of byte array while ignoring header bytes
3. **Testbench Setup**: Generate unique 32-bit addresses using `unique()` and `shuffle()`
4. **Scoreboard**: Sort error events by timestamp using custom `sort()` criteria
5. **Memory Analysis**: Find first and last occurrences of a specific data pattern in a memory dump

## Pro Tips
1. Combine methods for powerful operations:
   ```SV
   // Get sorted unique even numbers
   int processed[] = orig_array.find(x) with (x%2 == 0).unique().sort();
   ```
2. Use array methods in constraints:
   ```SV
   constraint unique_values { data.unique().size() == data.size(); }
   ```
3. Handle large arrays efficiently:
   ```SV
   if (big_array.sum() with (x > threshold)) > MAX_SUM) ... 
   ```
