# Array Manipulation

## Introduction
SystemVerilog provides powerful array manipulation capabilities for both static and dynamic arrays. While manipulation methods primarily operate on **dynamic arrays**, **queues**, and **associative arrays**, understanding array indexing is crucial for all array types. This guide covers fundamental access techniques and advanced manipulation methods optimized for verification and RTL design.

## Array Indexing Fundamentals
SystemVerilog supports complex multidimensional arrays with both packed and unpacked dimensions. Proper indexing is essential for hardware modeling and data processing.

### Example Array Structure
```SV
logic [127:0][7:0] my_array [8][64][32];
```

#### Dimension Breakdown:
1. **Unpacked Dimensions** (Storage structure):
   - `[8][64][32]`: 3D array with 8×64×32 = 16,384 elements
2. **Packed Dimensions** (Bit pattern):
   - `[127:0][7:0]`: 128×8 = 1,024 bits per element

### Indexing Techniques
| Access Level                | Example                          | Description                              |
|-----------------------------|----------------------------------|------------------------------------------|
| **Full element**            | `my_array[2][5][17]`             | Gets 128-byte element at position 2,5,17 |
| **Single byte**             | `my_array[1][3][20][45]`         | Accesses byte 45 within element          |
| **Single bit**              | `my_array[0][10][5][120][3]`     | Gets bit 3 of byte 120                   |
| **Byte range**              | `my_array[4][25][10][0:15]`      | Extracts first 16 bytes                  |
| **Bit slice**               | `my_array[7][63][31][127][3:0]`  | Gets lower nibble of last byte           |

### Iteration Patterns
```SV
// Unpacked dimensions iteration
foreach (my_array[i,j,k]) begin
  // Packed dimensions iteration
  foreach (my_array[i][j][k][l]) begin
    $display("Bank %0d, Row %0d, Col %0d, Byte %0d: %h", 
             i, j, k, l, my_array[i][j][k][l]);
  end
end
```

### Key Considerations
1. **Packed Order**: Rightmost dimension changes fastest (`[7:0]` bits vary first)
2. **Memory Efficiency**: Packed arrays use contiguous bits, unpacked use pointer arrays
3. **Synthesis**: Unpacked arrays often map to RAM structures, packed to registers

## Array Methods Overview
*Applies to dynamic arrays, queues, and associative arrays*

### Searching & Filtering Methods
| Method                 | Description                                                                 | Example with Expression                  |
|------------------------|-----------------------------------------------------------------------------|------------------------------------------|
| **`find()`**           | Returns all elements matching the condition                                 | `array.find(x) with (x > 5)`             |
| **`find_index()`**     | Returns indices of matching elements                                        | `array.find_index(x) with (x % 2 == 0)`  |
| **`find_first()`**     | Returns first matching element                                              | `array.find_first(x) with (x < 0)`       |
| **`find_last()`**      | Returns last matching element                                               | `array.find_last(x) with (x == 255)`     |
| **`unique()`**         | Returns unique element values                                               | `array.unique()`                         |
| **`unique_index()`**   | Returns indices of first occurrence of unique values                        | `array.unique_index()`                   |

### Sorting & Ordering Methods
| Method                 | Description                                                                 | Example with Custom Sort                 |
|------------------------|-----------------------------------------------------------------------------|------------------------------------------|
| **`sort()`**           | Sorts elements in ascending order (modifies original array)                 | `array.sort() with (x < y)`              |
| **`rsort()`**          | Sorts elements in descending order                                          | `array.rsort() with (item > item)`       |
| **`reverse()`**        | Reverses element order in-place                                             | `array.reverse()`                        |
| **`shuffle()`**        | Randomizes element order                                                    | `array.shuffle()`                        |

### Mathematical Operations
| Method                 | Description                                                                 | Note                                     |
|------------------------|-----------------------------------------------------------------------------|------------------------------------------|
| **`sum()`**            | Returns sum of all elements                                                 | Auto-casts to array type                 |
| **`product()`**        | Returns product of all elements                                             | Use `longint` to avoid overflow          |
| **`min()`**            | Returns smallest element value                                              | Works with `with` clauses                |
| **`max()`**            | Returns largest element value                                               | Supports complex expressions             |

### Bitwise Operations
| Method                 | Description                                                                 | Typical Use Case                         |
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
names.sort() with (x.len());  // Sort by string length ascending
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
// Returns indices of first unique occurrences: {0, 1, 3, 5}
```

### 5. Multi-method Chaining
```SV
int values[] = {8, 3, 5, 8, 2, 5};
int result = values.unique().sum();  // Unique values: {8,3,5,2} → Sum=18
```

## Key Considerations
1. **Modification Warnings**: Methods like `sort()`, `reverse()`, and `shuffle()` modify original arrays
2. **Static Array Limits**: Built-in methods only work with dynamic arrays/queues/associative arrays
3. **`with` Clause Flexibility**: Supports complex expressions:
   ```SV
   struct {int age; string name;} people[];
   people.sort() with (x.age);  // Sort structs by age
   ```
4. **Null Handling**: Methods return empty arrays when no matches found
5. **Performance**: Associative array methods have O(n log n) complexity

## Practical Exercises
1. **Memory Analysis**: Extract specific bytes from `my_array[8][64][32]` structure
2. **Data Validation**: Find transactions > $1000 in a financial record queue
3. **Packet Processing**: Calculate XOR checksum while ignoring header bytes
4. **Testbench Setup**: Generate unique 32-bit addresses using `unique()` + `shuffle()`
5. **Error Tracking**: Sort error events by timestamp with custom `sort()` criteria

## Pro Tips
1. **Combined Indexing/Methods**:
   ```SV
   // Extract bytes 64-127 from all array elements
   logic [63:0][7:0] upper_half = my_array[][][][64:127];
   ```
2. **Efficient Searches**:
   ```SV
   // Find first occurrence in 2D array
   int matrix[][];
   int found = matrix.find_first() with (item inside {[10:20]}));
   ```
3. **Conditional Summation**:
   ```SV
   // Sum only positive values
   int total = values.sum() with (item > 0 ? item : 0);
   ```
4. **Synthesis-Friendly Code**:
   ```SV
   // Use packed arrays for bitwise operations in RTL
   logic [7:0][31:0] reg_file;
   assign parity_bit = reg_file[3].xor();
   ```
