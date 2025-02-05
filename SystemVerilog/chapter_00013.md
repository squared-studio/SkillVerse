# Randomization

## Introduction
SystemVerilog randomization enables advanced verification methodologies through **constrained random verification**:
- Generates diverse stimulus scenarios
- Achieves high functional coverage
- Mimics real-world variability
- Reduces manual test case creation

Key components:
1. **Random Variables**: Specify what to randomize
2. **Constraints**: Define legal value ranges/relationships
3. **Control Methods**: Manage randomization process

## Random Variable Types
| Type      | Behavior                   | Use Case                  |
|-----------|----------------------------|---------------------------|
| `rand`    | Uniform distribution       | General value generation  |
| `randc`   | Cyclic permutation         | Unique value generation   |
| `rand*`   | Combined with class fields | Complex data structures   |

### Class-Based Example
```SV
class network_packet;
  rand bit [31:0] source_ip;
  randc bit [15:0] packet_id;
  rand bit [7:0] payload[];

  function new(int max_size=64);
    payload = new[max_size];
  endfunction
endclass
```

## Constraint Specification
### Constraint Types
```SV
class ethernet_frame;
  rand bit [11:0] length;
  rand bit [7:0]  payload[];
  rand bit        crc_error;

  // Range constraint
  constraint valid_length {
    length inside {[64:1518]};
  }

  // Conditional constraint
  constraint payload_size {
    payload.size() == length - 18;
  }

  // Probability distribution
  constraint error_dist {
    crc_error dist {0 := 95, 1 := 5};
  }

  // Cross-variable relationship
  constraint frame_consistency {
    solve length before payload;
  }
endclass
```

### Advanced Features
1. **Soft Constraints**: Can be overridden
   ```SV
   constraint flexible_size {
     soft payload.size() inside {[64:256]};
   }
   ```
2. **Implication**
   ```SV
   constraint jumbo_frames {
     (length > 1518) -> payload.size() > 1500;
   }
   ```

## Randomization Control
### Core Methods
```SV
class test_generator;
  rand ethernet_frame frame;
  int seed = 12345;

  function void configure();
    // Seed management
    srandom(seed);

    // Randomization control
    if(!frame.randomize()) begin
      $error("Frame randomization failed");
    end

    // Partial randomization
    frame.randomize(length) with {length > 1000;};
  endfunction
endclass
```

### Special Methods
1. **pre_randomize()**: Callback before randomization
2. **post_randomize()**: Callback after randomization
3. **randomize(null)**: Randomize all class properties

## Verification Integration
### Typical Testbench Structure
```SV
module tb;
  test_generator gen;
  int test_count = 100;

  initial begin
    gen = new();
    gen.seed = $urandom();

    repeat(test_count) begin
      if (!gen.randomize()) begin
        $fatal("Test randomization failed");
      end
      send_to_dut(gen.frame);
      check_response();
    end
  end
endmodule
```

### Coverage-Driven Example
```SV
class coverage_collector;
  covergroup frame_cg;
    length_cp: coverpoint frame.length {
      bins small = {[64:512]};
      bins medium = {[513:1024]};
      bins large = {[1025:1518]};
    }
    error_cp: coverpoint frame.crc_error;
  endgroup

  function new();
    frame_cg = new();
  endfunction

  function void sample();
    frame_cg.sample();
  endfunction
endclass
```

## Best Practices
1. **Constraint Design**
   - Use descriptive constraint names
   - Avoid circular dependencies
   - Prioritize constraints with `solve...before`

2. **Seed Management**
   - Log seeds for reproducibility
   - Use plusarg for seed configuration
   ```SV
   if (!$value$plusargs("SEED=%d", seed)) begin
     seed = 42;
   end
   ```

3. **Debugging**
   - Use `rand_mode()` to disable constraints
   - Print constraints with `constraint_mode()`
   - Enable debug messages:
     ```SV
     class debug_class;
       constraint debug_c { $display("Randomizing value: %0d", var); }
     endclass
     ```

## Exercises
1. **Basic Packet Generator**
   Create an `ip_packet` class with:
   - Random source/destination addresses
   - Constrained packet length (20-1500 bytes)
   - Random protocol field (TCP/UDP/ICMP)

2. **Advanced Constraints**
   Implement a `memory_transaction` class with:
   - Random address within memory map regions
   - Read/write operation distribution (70% read)
   - Burst length constraints (power-of-2 values)

3. **Error Injection**
   Develop an `error_generator` with:
   - Configurable error probability
   - Correlated error types (single-bit, burst, CRC)
   - Error position constraints in data stream

4. **Coverage Integration**
   Create a self-checking testbench that:
   - Generates 1000 random USB packets
   - Collects functional coverage
   - Verifies all constraints are exercised
   - Reports coverage statistics

