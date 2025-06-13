// allow a verbose/silent output toggle, which can be disabled entirely in synthesis
`ifndef SYNTHESIS
    `define VEBROSE(args) if (verbose_level > 1) $display(__VA_ARGS__)
    `define ERROR(args) if (verbose_level > 0) $error(__VA_ARGS__)
`else 
    `define VERBOSE(args)
`endif
