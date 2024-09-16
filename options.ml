module Self = Plugin.Register (struct
  let name = "cegarmc"
  let shortname = "mc"
  let help = "query a C model checker within frama-c."
end)

module Enabled = Self.False (struct
  let option_name = "-cegarmc"
  let help = "when on (off by default), enable Cegarmc."
end)

module OutputFile = Self.String (struct
  let option_name = "-cegarmc-output"
  let default = "-"
  let arg_name = "output-file"
  let help = "file where the message is output (default: output to the console)"
end)
