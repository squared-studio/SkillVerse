# Built-in System Tasks and System Functions in SystemVerilog

SystemVerilog provides essential **system tasks and functions** to streamline debugging, simulation control, and waveform analysis. Below is a detailed breakdown of their usage, with examples and exercises.

## **Display Tasks**  
These tasks print messages or variable values during simulation for debugging purposes.

### 1. **`$display`**  
Prints formatted text to the console **immediately** when called.  
- **Format Specifiers**:  
  - `%t`: Simulation time.  
  - `%d`: Decimal value.  
  - `%b`: Binary value.  
  - `%h`: Hexadecimal value.  

```SV
module display_example;
  initial begin
    int value = 42;
    $display("[%0t] Value = %0d (binary: %b)", $time, value, value);
    // Output: "[0] Value = 42 (binary: 101010)"
  end
endmodule
```

### 2. **`$monitor`**  
Continuously monitors variables and prints updates **whenever they change**.  
- Only **one `$monitor`** can be active at a time.  
- Use `$monitoron`/`$monitoroff` to control monitoring.

```SV
module monitor_example;
  reg [3:0] a, b;
  initial begin
    $monitor("Time=%0t: a=%0d, b=%0d", $time, a, b);
    a = 0; b = 0;
    #5 a = 5;   // Triggers $monitor
    #5 b = 10;  // Triggers $monitor again
  end
endmodule
```
**Output**:  
```
Time=0: a=0, b=0  
Time=5: a=5, b=0  
Time=10: a=5, b=10  
```

### 3. **`$strobe`**  
Prints values **at the end of the current time step**, after all assignments are settled.  
- Useful for capturing stable values after concurrent updates.

```SV
module strobe_example;
  reg [3:0] data;
  initial begin
    data = 0;
    #5 data = 5;
    $strobe("[Strobe] Time=%0t, Data=%0d", $time, data); // Output: "[Strobe] Time=5, Data=5"
  end
endmodule
```

## **Wavedump Tasks**  
Generate **Value Change Dump (VCD)** files for waveform analysis.

### 1. **`$dumpfile`**  
Specifies the name of the waveform file.  
```SV
module dumpfile_example;
  initial begin
    $dumpfile("signals.vcd"); // Creates 'signals.vcd'
  end
endmodule
```

### 2. **`$dumpvars`**  
Selects signals to dump into the VCD file.  
- **Arguments**:  
  - `$dumpvars(0, module_name)`: Dump **all** variables in `module_name`.  
  - `$dumpvars(1, signal)`: Dump a specific signal.  

```SV
module dumpvars_example;
  reg clk, enable;
  initial begin
    $dumpfile("waveform.vcd");
    $dumpvars(0, dumpvars_example); // Dump ALL variables in this module
    clk = 0;
    enable = 1;
    forever #5 clk = ~clk;
  end
endmodule
```

## **Time-Related Functions**  
Retrieve simulation time with varying precision.

### 1. **`$time`**  
Returns current simulation time as a **64-bit integer**.  
```SV
module time_example;
  initial begin
    #7.5;
    $display("64-bit Time: %0t", $time); // Output: "64-bit Time: 7"
  end
endmodule
```

### 2. **`$stime`**  
Returns current time as a **32-bit integer** (truncates for large simulations).  
```SV
module stime_example;
  initial begin
    #100000;
    $display("32-bit Time: %0d", $stime); // Output: "32-bit Time: 100000"
  end
endmodule
```

### 3. **`$realtime`**  
Returns time as a **real number** (supports fractional time steps).  
```SV
module realtime_example;
  initial begin
    #3.75;
    $display("Real Time: %0.2f", $realtime); // Output: "Real Time: 3.75"
  end
endmodule
```

## **Simulation Control Tasks**  
Control simulation execution flow.

### 1. **`$finish`**  
Terminates the simulation and closes the simulator.  
```SV
module finish_example;
  initial begin
    #10 $display("Done.");
    $finish; // Ends simulation here
  end
endmodule
```

### 2. **`$stop`**  
Pauses the simulation, allowing you to resume later (e.g., in interactive mode).  
```SV
module stop_example;
  initial begin
    #20 $display("Pausing simulation...");
    $stop; // Simulation pauses here
    #10 $display("Resumed."); // Never executed unless resumed manually
  end
endmodule
```

### 3. **`$exit`**  
Exits the simulator immediately (tool-dependent behavior).  
```SV
module exit_example;
  initial begin
    #5 $exit; // Simulator terminates abruptly
  end
endmodule
```

## **Exercises with Solutions**  
1. **Modify `$display` to include `$time`:**  
   ```SV
   initial $display("Time: %0t", $time);
   ```

2. **Add `b` to `$monitor`:**  
   ```SV
   $monitor("a=%0d, b=%0d", a, b);
   ```

3. **Use `$strobe` with a variable:**  
   ```SV
   reg [3:0] count;
   initial begin
     count = 5;
     #1 count = 10;
     $strobe("Strobe: count=%0d", count); // Output: "Strobe: count=10"
   end
   ```

4. **Create a `$dumpfile`:**  
   ```SV
   module my_module;
     initial $dumpfile("my_wave.vcd");
   endmodule
   ```

5. **Add variables to `$dumpvars`:**  
   ```SV
   $dumpvars(0, module_name); // Dumps all variables in 'module_name'
   ```

6. **Display `$time` at multiple points:**  
   ```SV
   initial begin
     $display("T1: %0t", $time);
     #10 $display("T2: %0t", $time);
   end
   ```

7. **Compare `$stime` vs. `$time`:**  
   - `$time` is 64-bit; `$stime` truncates to 32 bits for large values.

8. **Use `$realtime` for precision:**  
   ```SV
   #3.75 $display("%0.2f", $realtime); // Output: "3.75"
   ```

9. **Delay before `$finish`:**  
   ```SV
   initial #50 $finish;
   ```

10. **Resume after `$stop`:**  
    - In tools like ModelSim, use `run -continue` to resume.

11. **Compare `$exit` and `$finish`:**  
    - `$finish` gracefully ends the simulation; `$exit` may force-terminate the tool.
