(load-file "emacs-epigram-interpreted.el")

(setq epigram-executable (concat default-directory "ghci-epigram"))

(install-epigram)
(with-current-buffer underneath-buffer
  (insert ":l Main\n")
  (insert "main\n")
  (comint-send-input)
  (switch-to-buffer epigram-buffer)
)

