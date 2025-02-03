# Array

## Introduction
Arrays in SystemVerilog are versatile data structures used to store collections of elements. They come in several types, each suited for specific use cases:
- **Packed Arrays**: Contiguous bits for efficient bitwise operations (e.g., registers).
- **Unpacked Arrays**: Collections of individual elements (e.g., memory blocks).
- **Fixed-Size Arrays**: Size determined at compile time.
- **Dynamic Arrays**: Size adjustable at runtime.
- **Associative Arrays**: Key-value pairs with flexible indexing.
- **Queues**: Ordered lists with fast insertion/deletion at ends.

## Packed vs. Unpacked Arrays

### Packed Array
- Stored as a single contiguous bit vector.
- Ideal for bit-level operations and hardware modeling.
- Can have multiple dimensions (e.g., `[row][col]`).

```SV
logic [3:0][7:0] packed_2d;  // 4x8 bit matrix (32 bits total)
packed_2d = 32'hA5A5A5A5;     // Initialize with hexadecimal value
```

### Unpacked Array
- Elements stored separately in memory.
- Dimensions declared after the identifier.
```SV
int unpacked_array [4];       // 4 integer elements
unpacked_array = '{1, 2, 3, 4};  // Initialize with values
```

## Fixed-Size Array
- Size defined at compile time.
- Supports array manipulation methods (e.g., `sort`, `sum`).

```SV
int fixed_array [0:3] = '{4, 3, 2, 1};
fixed_array.sort();  // Sorts to '{1, 2, 3, 4}
```

### Methods for Fixed-Size Arrays
| Method     | Description                          | Example                             |
|------------|--------------------------------------|-------------------------------------|
| `size`     | Returns number of elements           | `int s = fixed_array.size();`       |
| `sort`     | Sorts elements in ascending order    | `fixed_array.sort();`               |
| `reverse`  | Reverses element order               | `fixed_array.reverse();`            |
| `sum`      | Returns sum of all elements          | `int total = fixed_array.sum();`    |
| `rsort`    | Sorts in descending order            | `fixed_array.rsort();`              |

## Dynamic Array
- Size can be changed at runtime using `new[]`.
- Memory must be allocated before use.

```SV
int dynamic_array [];
initial begin
  dynamic_array = new[5];        // Allocate 5 elements
  dynamic_array = '{5, 4, 3, 2, 1};
  dynamic_array = new[10] (dynamic_array);  // Resize to 10, copy old values
end
```

### Methods for Dynamic Arrays
| Method     | Description                          | Example                             |
|------------|--------------------------------------|-------------------------------------|
| `size`     | Returns current size                 | `int s = dynamic_array.size();`     |
| `new[N]`   | Allocates `N` elements               | `dynamic_array = new[20];`          |
| `delete`   | Deallocates memory (size becomes 0)  | `dynamic_array.delete();`           |
| `sort`     | Sorts elements                       | `dynamic_array.sort();`             |

## Associative Array
- Indexed by keys of any data type (e.g., strings, integers).
- Efficient for sparse data storage.

```SV
int assoc_array [string];
initial begin
  assoc_array["Alice"] = 42;
  assoc_array["Bob"] = 99;
  if (assoc_array.exists("Alice")) 
    $display("Alice: %d", assoc_array["Alice"]);
end
```

### Methods for Associative Arrays
| Method     | Description                          | Example                             |
|------------|--------------------------------------|-------------------------------------|
| `num`      | Returns number of entries            | `int n = assoc_array.num();`        |
| `delete`   | Removes all entries                  | `assoc_array.delete();`             |
| `delete(x)`| Removes entry at key `x`             | `assoc_array.delete("Alice");`      |
| `exists(x)`| Checks if key `x` exists             | `if (assoc_array.exists("Bob"))...` |
| `first(ref x)` | Assigns first key to `x`        | `string key; assoc_array.first(key);` |
| `next(ref x)`  | Assigns next key to `x`         | `assoc_array.next(key);`            |

## Queue
- Ordered collection with fast access at both ends.
- Automatically resizes as elements are added/removed.

```SV
int queue [$] = '{1, 2, 3};  // Initialize with values
initial begin
  queue.push_back(4);   // Queue: '{1,2,3,4}
  queue.push_front(0);  // Queue: '{0,1,2,3,4}
  queue.pop_back();     // Queue: '{0,1,2,3}
end
```

### Methods for Queues
| Method        | Description                          | Example                     |
|---------------|--------------------------------------|-----------------------------|
| `size`        | Returns number of elements           | `int s = queue.size();`     |
| `insert(i,x)` | Inserts `x` at index `i`             | `queue.insert(2, 5);`       |
| `delete`      | Clears all elements                  | `queue.delete();`           |
| `pop_front`   | Removes and returns first element    | `int x = queue.pop_front();`|
| `push_back(x)`| Adds `x` to the end                  | `queue.push_back(10);`      |
| `sort`        | Sorts elements in place              | `queue.sort();`             |

## Exercises
1. **Packed Array**: Declare a 12-bit packed array and initialize it with `0xA3C`.
   ```SV
   logic [11:0] packed_arr = 12'hA3C;
   ```
2. **Unpacked Array**: Create an unpacked array of 4 strings and print each element.
   ```SV
   string names [4] = '{"Alice", "Bob", "Charlie", "Dana"};
   foreach (names[i]) $display("%s", names[i]);
   ```
3. **Fixed-Size Array**: Declare a 5-element array, assign values, and compute their sum.
   ```SV
   int arr [5] = '{10, 20, 30, 40, 50};
   $display("Sum: %d", arr.sum());
   ```
4. **Dynamic Array**: Allocate a dynamic array with 8 elements and fill it with even numbers.
   ```SV
   int dyn_arr [];
   dyn_arr = new[8];
   foreach (dyn_arr[i]) dyn_arr[i] = i*2;
   ```
5. **Associative Array**: Store ages of 3 people and check if "John" exists.
   ```SV
   int ages [string];
   ages["Alice"] = 30;
   ages["Bob"] = 25;
   if (!ages.exists("John")) $display("John not found!");
   ```
6. **Queue**: Create a queue, push 3 elements, reverse it, and pop the first element.
   ```SV
   int q [$] = '{1, 2, 3};
   q.reverse();       // Queue: '{3,2,1}
   q.pop_front();     // Removes 3
   ```
