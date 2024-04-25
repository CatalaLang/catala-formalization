
(rule
  (alias install)
  (deps (file common.v) (file common.vo))
  (action 
    (with-stdout-to common.html
    (run %{bin:alectryon} --copy-assets none -R . Catala --frontend coq --backend webpage
      common.v -o common.html))))

(rule
  (alias install)
  (deps (file continuations.v) (file continuations.vo))
  (action 
    (with-stdout-to continuations.html
    (run %{bin:alectryon} --copy-assets none -R . Catala --frontend coq --backend webpage
      continuations.v -o continuations.html))))

(rule
  (alias install)
  (deps (file sequences.v) (file sequences.vo))
  (action 
    (with-stdout-to sequences.html
    (run %{bin:alectryon} --copy-assets none -R . Catala --frontend coq --backend webpage
      sequences.v -o sequences.html))))

(rule
  (alias install)
  (deps (file simulation_cred_to_sred.v) (file simulation_cred_to_sred.vo))
  (action 
    (with-stdout-to simulation_cred_to_sred.html
    (run %{bin:alectryon} --copy-assets none -R . Catala --frontend coq --backend webpage
      simulation_cred_to_sred.v -o simulation_cred_to_sred.html))))

(rule
  (alias install)
  (deps (file simulation_sred_to_cred.v) (file simulation_sred_to_cred.vo))
  (action 
    (with-stdout-to simulation_sred_to_cred.html
    (run %{bin:alectryon} --copy-assets none -R . Catala --frontend coq --backend webpage
      simulation_sred_to_cred.v -o simulation_sred_to_cred.html))))

(rule
  (alias install)
  (deps (file small_step.v) (file small_step.vo))
  (action 
    (with-stdout-to small_step.html
    (run %{bin:alectryon} --copy-assets none -R . Catala --frontend coq --backend webpage
      small_step.v -o small_step.html))))

(rule
  (alias install)
  (deps (file syntax.v) (file syntax.vo))
  (action 
    (with-stdout-to syntax.html
    (run %{bin:alectryon} --copy-assets none -R . Catala --frontend coq --backend webpage
      syntax.v -o syntax.html))))

(rule
  (alias install)
  (deps (file tactics.v) (file tactics.vo))
  (action 
    (with-stdout-to tactics.html
    (run %{bin:alectryon} --copy-assets none -R . Catala --frontend coq --backend webpage
      tactics.v -o tactics.html))))

(rule
  (alias install)
  (deps (file trans.v) (file trans.vo))
  (action 
    (with-stdout-to trans.html
    (run %{bin:alectryon} --copy-assets none -R . Catala --frontend coq --backend webpage
      trans.v -o trans.html))))

(rule
  (alias install)
  (deps (file typing.v) (file typing.vo))
  (action 
    (with-stdout-to typing.html
    (run %{bin:alectryon} --copy-assets none -R . Catala --frontend coq --backend webpage
      typing.v -o typing.html))))

(rule
 (deps)
 (targets alectryon.css alectryon.js pygments.css)
 (action
  (no-infer
   (progn
    (write-file dummy.v "")
    (run %{bin:alectryon} dummy.v)))))
