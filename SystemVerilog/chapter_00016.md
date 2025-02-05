# File Operations

## Introduction
File operations in SystemVerilog enable interaction with external files for various applications including:
- Reading test vectors and configuration data
- Logging simulation results and debug information
- Storing intermediate processing data
- Generating post-simulation reports

Proper file handling is essential for data-driven verification and maintaining simulation traceability.

## File Handling Basics

### Opening Files
Use `$fopen` to obtain a file handle. Supported modes include:
| Mode | Description                          |
|------|--------------------------------------|
| "r"  | Read (file must exist)               |
| "w"  | Write (creates/truncates file)       |
| "a"  | Append (creates/appends to file)     |
| "r+" | Read/update (existing file)          |
| "w+" | Write/update (creates/truncates)     |

### Closing Files
Always use `$fclose` to release file resources after operations.

## Reading from Files

### Line-by-Line Reading with $fgets
```SV
module file_read;
  int fd;
  string line;
  initial begin
    fd = $fopen("data.txt", "r");
    if (!fd) begin
      $error("Failed to open file");
      $finish;
    end

    while ($fgets(line, fd)) begin  // Returns 0 on error/EOF
      $display("[LINE] %s", line);
    end

    $fclose(fd);
  end
endmodule
```

### Formatted Reading with $fscanf
```SV
module formatted_read;
  int fd, value;
  initial begin
    fd = $fopen("values.txt", "r");
    if (!fd) $fatal(1, "File open error");

    while ($fscanf(fd, "%d", value) == 1) begin
      $display("Read value: %0d", value);
    end

    $fclose(fd);
  end
endmodule
```

**Best Practices:**
- Check `$fopen` return value explicitly (0 indicates failure)
- Prefer `$fgets` return value checks over `$feof` for loop control
- Use `$fscanf` return value to verify successful conversions

## Writing to Files

### Basic Writing Operations
```SV
module file_write;
  int fd;
  initial begin
    fd = $fopen("output.log", "w");
    if (!fd) begin
      $error("Cannot create file");
      return;
    end

    // $fwrite without automatic newline
    $fwrite(fd, "Simulation started at %0t", $time);

    // $fdisplay with automatic newline
    $fdisplay(fd, "Config: mode=%0d, speed=%0d", 2, 45);

    $fclose(fd);
  end
endmodule
```

### Key Differences:
| Function  | Newline | Formatting           | Typical Use Case          |
|-----------|---------|----------------------|---------------------------|
| `$fwrite` | No      | Supports format spec | Structured data output    |
| `$fdisplay`| Yes    | Full formatting      | Human-readable logging    |
| `$fstrobe` | Yes    | Postponed execution  | Final value recording     |

## Advanced File Operations

### Multi-Channel Output
```SV
module multi_output;
  int logfile, console = 1<<31;  // Use 32'h8000_0000 for stdout
  initial begin
    logfile = $fopen("activity.log", "w");

    // Write to both console and logfile
    $fwrite(logfile | console, "System initialized\n");

    $fclose(logfile);
  end
endmodule
```

### Binary File Access
```SV
module binary_ops;
  int fd;
  byte data[];
  initial begin
    // Write binary data
    fd = $fopen("data.bin", "wb");
    data = {8'hDE, 8'hAD, 8'hBE, 8'hEF};
    foreach(data[i]) $fwrite(fd, "%c", data[i]);
    $fclose(fd);

    // Read binary data
    fd = $fopen("data.bin", "rb");
    foreach(data[i]) void'($fscanf(fd, "%c", data[i]));
    $fclose(fd);
  end
endmodule
```

## Comprehensive Function Reference

| Function    | Description                                  | Return Value              |
|-------------|----------------------------------------------|---------------------------|
| `$fopen`    | Opens file, returns handle or 0              | File descriptor (int)     |
| `$fclose`   | Closes opened file                           | None                      |
| `$fgets`    | Reads string until newline                   | 0 (error/EOF), 1 (success)|
| `$fscanf`   | Reads formatted input                        | Number of matched items   |
| `$fread`    | Binary read into array                       | Number of bytes read      |
| `$fwrite`   | Writes formatted data without auto-newline   | None                      |
| `$fdisplay` | Writes formatted line with auto-newline      | None                      |
| `$feof`     | Checks for end-of-file                       | 1 (EOF), 0 (not EOF)      |
| `$ferror`   | Checks file error status                     | Error code (int)          |

## Error Handling Techniques

### Comprehensive File Check
```SV
module safe_write;
  int fd;
  initial begin
    fd = $fopen("critical.dat", "a");
    if (fd === 0) begin
      $error("File open failed: Code %0d", $ferror(fd));
      $fatal(1, "Cannot proceed without output file");
    end

    if ($fdisplay(fd, "New entry") != 0) begin
      $error("Write error: Code %0d", $ferror(fd));
    end

    $fclose(fd);
  end
endmodule
```

## Best Practices Checklist
1. Always verify `$fopen` return values
2. Use appropriate file modes (w vs a vs r+)
3. Close files explicitly with `$fclose`
4. Prefer `$fdisplay` for human-readable logs
5. Use `$fwrite` for precise format control
6. Check `$fscanf` return values for parsing validation
7. Utilize `$ferror` for diagnostic information
8. Consider file buffering strategies for large datasets

## Practical Exercises
1. **File Analysis**: Create a module that counts lines and words in a text file
2. **Data Logger**: Implement a timestamped simulation activity recorder
3. **Config Parser**: Develop a parameter parser that reads key=value pairs
4. **Binary Converter**: Write a utility that converts ASCII hex to binary files
5. **Error Handler**: Create a file wrapper module with automatic error recovery

```SV
// Sample Solution for Exercise 2 (Data Logger)
module timestamp_logger;
  int logfd;
  timeunit 1ns/1ps;

  initial begin
    logfd = $fopen("sim_times.log", "w");
    if (!logfd) $fatal(1, "Log file creation failed");

    fork
      begin
        #10ns;
        $fdisplay(logfd, "[%0t] Phase 1 Complete", $time);
      end
      begin
        #25ns;
        $fdisplay(logfd, "[%0t] Phase 2 Started", $time);
      end
    join

    $fclose(logfd);
  end
endmodule
```
