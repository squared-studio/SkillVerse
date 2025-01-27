# Procedural Blocks

SystemVerilog provides several types of procedural blocks to describe the behavior of hardware. These include `assign`, `always`, `always_comb`, `always_ff`, `always_latch`, `initial`, `final`, `function`, and `task`.

## assign
The `assign` statement is used for continuous assignments in combinational logic.
```SV
module assign_example;
    wire a, b, c;
    assign c = a & b;
endmodule
```

## always
The `always` block is used to describe behavior that should be executed repeatedly.
```SV
module always_example;
    reg clk;
    always #5 clk = ~clk;
endmodule
```

## always_comb
The `always_comb` block is used to describe combinational logic.
```SV
module always_comb_example;
    logic a, b, c;
    always_comb begin
        c = a & b;
    end
endmodule
```

## always_ff
The `always_ff` block is used to describe sequential logic with flip-flops.
```SV
module always_ff_example;
    logic clk, reset, q;
    always_ff @(posedge clk or posedge reset) begin
        if (reset)
            q <= 1'b0;
        else
            q <= ~q;
    end
endmodule
```

## always_latch
The `always_latch` block is used to describe latch-based logic.
```SV
module always_latch_example;
    logic enable, d, q;
    always_latch begin
        if (enable)
            q <= d;
    end
endmodule
```

## initial
The `initial` block is used to describe behavior that should be executed once at the beginning of the simulation.
```SV
module initial_example;
    initial begin
        $display("Simulation started");
        #10 $finish;
    end
endmodule
```

## final
The `final` block is used to describe behavior that should be executed once at the end of the simulation.
```SV
module final_example;
    final begin
        $display("Simulation ended");
    end
endmodule
```

## Exercise
1. Create a module that uses the `assign` statement to perform a continuous assignment.
2. Create a module that uses the `always` block to generate a clock signal.
3. Create a module that uses the `always_comb` block to describe combinational logic.
4. Create a module that uses the `always_ff` block to describe sequential logic with flip-flops.
5. Create a module that uses the `always_latch` block to describe latch-based logic.
6. Create a module that uses the `initial` block to print a message at the beginning of the simulation.
7. Create a module that uses the `final` block to print a message at the end of the simulation.
