(load "emacs-epigram.elc")

(defun epigram-send-input ()
  (with-current-buffer underneath-buffer
    (cond ((equal "" epigram-queue))
          ((= (point) (point-max))
             (insert epigram-queue)
             (setq epigram-queue "")
             (comint-send-input)))
))

(defun epigram-queue-input (x)
  (setq epigram-queue (concat epigram-queue x "\n"))
  (cond (epigram-ready (epigram-send-input)))
)

(define-derived-mode epigram-mode fundamental-mode "Epigram"
;  (setq modeline-format "(epigram-cursor %l %c)")
;  (make-local-hook 'mouse-track-down-hook)
  (make-local-hook 'mouse-track-click-hook)
  (make-local-variable 'epigram-point)
  (make-local-variable 'epigram-xy-point)
  (make-local-variable 'epigram-name)
  (setq mouse-track-click-hook
    '(epigram-click-hook)); default-mouse-track-click-hook))
;  (setq mouse-track-down-hook
;    '(epigram-down-hook)); default-mouse-track-down-hook))
  (setq truncate-lines t)
  (toggle-read-only 1)
  (set-keymap-default-binding epigram-mode-map 'epigram-keystroke)
  (local-set-key [button1] 'mouse-track)
)


(defun epigram-keystroke () (interactive)
  (epigram-queue-input (epigram-event (elt (this-command-keys) 0)))
  ; (with-current-buffer underneath-buffer
    ; (goto-char (point-max))
    ; (insert (epigram-event (elt (this-command-keys) 0)))
    ; (insert "\n")
    ; (comint-send-input)
  ; )
)

(defun epigram-idle-hook ()
  (with-current-buffer underneath-buffer
    (let ((keeper (point)))
      (goto-char underneath-do-from)
      (setq underneath-do-from (doit-or-not))
      (goto-char keeper)
    )
  )
  (epigram-send-input)
)

(defun install-epigram ()
  (interactive)
  (comint-run epigram-executable)
  (setq underneath-buffer (current-buffer))
  (setq underneath-do-from (point))
  (setq yard-buffer
     (generate-new-buffer (generate-new-buffer-name "*Yard*")))
  (add-hook 'pre-idle-hook 'epigram-idle-hook)
  (setq epigram-buffer
     (generate-new-buffer (generate-new-buffer-name "*Epigram*")))
  (setq epigram-queue "")
  (setq epigram-ready t)
  (epigram (epigram-mode))
  (epigram (setq epigram-name "Epigram"))
  (setq horace-buffer
     (generate-new-buffer (generate-new-buffer-name "*Horace*")))
  (horace (epigram-mode))
  (horace (setq epigram-name "Horace"))
  (global-set-key [(control c) (control e)] 'glom-epigram) ; yuk
  (global-set-key [(control c) (control s)] 'shed-rectangle) ; yuk
  (global-set-key [(control c) (control b)] 'group-rectangle) ; yuk
  (global-set-key [(control c) (control c)] 'blat-epigram) ; yuk
  (global-set-key [(control c) (control r)] 'blat-region-epigram) ; yuk
  (global-set-key [(control c) r] 'blat-rectangle-epigram) ; yuk
)

;(defun glom-epigram () (interactive)
;  (delete-buffer-contents)
;  (insert-buffer epigram-buffer)
;)

(defun collapse-module ()
  (cond ((re-search-forward
          "^----*\n\\( *begin *\\([^ \n]*\\).*\n\\(.\\|\n\\)*end \\2.*\\)"
          nil t)
         (setq epigram-include-name (match-string 2))
         (goto-char (match-beginning 1))
         (delete-region (match-beginning 1) (match-end 1))
         (insert "include " epigram-include-name)
         t)
        (t nil)
) )

(defun glom-epigram () (interactive)
  (with-current-buffer yard-buffer
    (delete-buffer-contents)
    (insert-buffer epigram-buffer)
    (goto-char (point-min))
    (while (collapse-module))
  )
  (delete-buffer-contents)
  (insert-buffer yard-buffer)
)

;(defun blat-epigram () (interactive)
;  (setq blat-buffer (current-buffer))
;  (with-current-buffer underneath-buffer
;    (insert "data\n")
;    (insert-buffer blat-buffer)
;    (goto-char (point-max))
;    (cond ((> (current-column) 0) (insert "\n")))
;    (insert "][][][][][\n")
;    (comint-send-input)
;  )
;)

(defun blat-epigram () (interactive)
  (setq blat-buffer (current-buffer))
  (with-current-buffer yard-buffer
    (delete-buffer-contents)
    (insert-buffer blat-buffer)
  )
  (expand-and-blat-yard)
)

;(defun blat-region-epigram () (interactive)
;  (copy-region-as-kill (point) (mark t))
;  (with-current-buffer underneath-buffer
;    (insert "data\n")
;    (yank)
;    (goto-char (point-max))
;    (cond ((> (current-column) 0) (insert "\n")))
;    (insert "][][][][][\n")
;    (comint-send-input)
;  )
;)

(defun blat-region-epigram () (interactive)
  (copy-region-as-kill (point) (mark t))
  (with-current-buffer yard-buffer
    (delete-buffer-contents)
    (yank)
  )
  (expand-and-blat-yard)
)

;(defun blat-rectangle-epigram () (interactive)
;  (cond ((> (point) (mark t))
;           (setq epi-rect (extract-rectangle (mark t) (point))))
;        (t (setq epi-rect (extract-rectangle (point) (mark t)))))
;  (with-current-buffer underneath-buffer
;    (insert "data\n")
;    (insert-rectangle epi-rect)
;    (goto-char (point-max))
;    (cond ((> (current-column) 0) (insert "\n")))
;    (insert "][][][][][\n")
;    (comint-send-input)
;  )
;)

(defun blat-rectangle-epigram () (interactive)
  (cond ((> (point) (mark t))
           (setq epi-rect (extract-rectangle (mark t) (point))))
        (t (setq epi-rect (extract-rectangle (point) (mark t)))))
  (with-current-buffer yard-buffer
    (delete-buffer-contents)
    (insert-rectangle epi-rect)
  )
  (expand-and-blat-yard)
)

(defun bracket-rectangle (o c r)
  (cond ((null r) nil)
        ((null (cdr r)) (cons (concat o (car r) c) nil))
        (t (cons (concat o (car r) "!") (bracket-rectangle "!" c (cdr r)))))
)

(defun shed-rectangle () (interactive)
  (cond ((> (point) (mark t)) (exchange-point-and-mark)))
  (setq epi-rect (delete-extract-rectangle (point) (mark t)))
  (insert-rectangle (bracket-rectangle "[" "]" epi-rect))
)

(defun group-rectangle () (interactive)
  (cond ((> (point) (mark t)) (exchange-point-and-mark)))
  (setq epi-rect (delete-extract-rectangle (point) (mark t)))
  (insert-rectangle (bracket-rectangle "(" ")" epi-rect))
)


(defun start-epigram ()
  (epigram (sneakily (delete-buffer-contents)))
)

(defmacro epigram (x) (list 'with-current-buffer 'epigram-buffer x))
(defmacro horace (x) (list 'with-current-buffer 'horace-buffer x))
(defmacro sneakily (x) (list 'progn
                             '(toggle-read-only -1)
                             x
                             '(toggle-read-only 1)))

(defun delete-buffer-contents ()
  (delete-region (point-min) (point-max))
)

(defun epigram-xy (x y)
  (setq epigram-point (point))
  (setq epigram-xy-point (goto-xy x y))
  (goto-char epigram-point)
  epigram-xy-point
)

(defun epigram-click-hook (e n)
  (mouse-set-point e)
  (epigram-cursor (line-number) (current-column))
  ()
)

;(defun epigram-click-hook (e n)
;  (eval (car (read-from-string generated-modeline-string)))
;  ()
;)

;(defun epigram-down-hook (e n)
;  (mouse-set-point e)
;  (redraw-modeline)
;  ()
;)

(defun epigram-cursor (l c)
  (epigram-queue-input
    (concat "click " epigram-name " "
      (number-to-string mouse-track-click-count) " "
      (number-to-string c) " " (number-to-string (- l 1))
    )
  )
  (try-to-make-buf-selected epigram-buffer)
)

(defun glom-begin ()
  (cond ((re-search-forward
          "^----*\n *begin *\\([^ \n]*\\).*\n" nil t)
         (match-string 1))
        (t nil)
) )

(defun glom-begins ()
  (with-current-buffer epigram-buffer
    (setq stash-point (point))
    (goto-char (point-min))
    (setq epigram-modules-begun ())
    (while (setq glom-begun (glom-begin))
      (setq epigram-modules-begun (cons glom-begun epigram-modules-begun))
    )
    (goto-char stash-point)
) )

(defun expand-include ()
  (cond ((re-search-forward
          "^\\(----*\n\\)\\( *include *\\([^ \n]*\\).*\n\\)" nil t)
         (setq epigram-include-rule (match-string 1))
         (setq epigram-include-name (match-string 3))
         (cond ((member epigram-include-name epigram-modules-begun))
               (t (setq epigram-modules-begun
                        (cons epigram-include-name epigram-modules-begun))
                  (delete-region (match-beginning 2) (match-end 2))
                  (insert "begin " epigram-include-name "\n"
                    epigram-include-rule)
                  (push-mark)
                  (insert epigram-include-rule
                    "end " epigram-include-name "\n")
                  (exchange-point-and-mark)
                  (pop-mark)
                  (zmacs-deactivate-region)
                  (insert-file-contents
                     (concat (file-name-sans-extension epigram-include-name)
                             ".epi"))
               ) )
         t)
        (t nil)
) )

(defun expand-and-blat-yard ()
  (glom-begins)
  (with-current-buffer yard-buffer
    (goto-char (point-min))
    (while (expand-include))
  )
  (with-current-buffer underneath-buffer
    (insert "data\n")
    (insert-buffer yard-buffer)
    (goto-char (point-max))
    (cond ((> (current-column) 0) (insert "\n")))
    (insert "][][][][][\n")
    (comint-send-input)
  )
)