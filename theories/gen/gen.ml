let generate_rules base =
  Printf.printf
    {|
(rule
  (alias install)
  (deps (file %s.v) (file %s.vo))
  (action 
    (with-stdout-to %s.html
    (run %%{bin:alectryon} --copy-assets none -R . Catala --frontend coq --backend webpage
      %s.v -o %s.html))))
|}
    base base base base base

let () =
  Sys.readdir "."
  |> Array.to_list
  |> List.sort String.compare
  |> List.filter_map (Filename.chop_suffix_opt ~suffix:".v")
  |> List.iter generate_rules;
  Printf.printf {|
(rule
 (deps)
 (targets alectryon.css alectryon.js pygments.css)
 (action
  (no-infer
   (progn
    (write-file dummy.v "")
    (run %%{bin:alectryon} dummy.v)))))
|}