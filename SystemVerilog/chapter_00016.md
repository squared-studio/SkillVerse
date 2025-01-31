# File Operators

## Introduction
File operators in SystemVerilog are used to read from and write to files. They provide a way to interact with external files for tasks such as logging simulation results, reading input data, and more.

## File Reading
File reading is performed using the `$fopen`, `$fgets`, and `$fscanf` functions.

### Example
```SV
module file_read_example;
  int file, r;
  string line;
  initial begin
    file = $fopen("input.txt", "r");
    if (file) begin
      while (!$feof(file)) begin
        r = $fgets(line, file);
        $display("Read line: %s", line);
      end
      $fclose(file);
    end else begin
      $display("Failed to open file");
    end
  end
endmodule
```

## File Writing
File writing is performed using the `$fopen`, `$fwrite`, and `$fclose` functions.

### Example
```SV
module file_write_example;
  int file;
  initial begin
    file = $fopen("output.txt", "w");
    if (file) begin
      $fwrite(file, "Hello, SystemVerilog!\n");
      $fclose(file);
    end else begin
      $display("Failed to open file");
    end
  end
endmodule
```

## File Handling Functions
SystemVerilog provides several built-in functions for file handling.

### Example
```SV
module file_handling_example;
  int file;
  initial begin
    file = $fopen("output.txt", "w");
    if (file) begin
      $fwrite(file, "Hello, SystemVerilog!\n");
      $fclose(file);
    end else begin
      $display("Failed to open file");
    end
  end
endmodule
```

### Common File Handling Functions
| Function      | Description                                 | Example                          |
|---------------|---------------------------------------------|----------------------------------|
| `$fopen`      | Opens a file                                | `file = $fopen("file.txt", "r");`|
| `$fclose`     | Closes a file                               | `$fclose(file);`                 |
| `$fgets`      | Reads a line from a file                    | `r = $fgets(line, file);`        |
| `$fscanf`     | Reads formatted input from a file           | `r = $fscanf(file, "%d", value);`|
| `$fwrite`     | Writes formatted output to a file           | `$fwrite(file, "Hello\n");`      |
| `$fdisplay`   | Writes formatted output to a file with newline | `$fdisplay(file, "Hello");`      |
| `$feof`       | Checks if the end of the file is reached    | `if ($feof(file)) ...`           |

## Exercises
1. Open a file and read its contents line by line.
2. Write a message to a file and close it.
3. Use `$fscanf` to read formatted input from a file.
4. Use `$fdisplay` to write formatted output to a file with a newline.

