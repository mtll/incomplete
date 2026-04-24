;;; incomplete.el --- Better Elisp completion -*- lexical-binding: t -*-

;; Author: David Feller
;; Keywords: lisp, completion

;; Package-Version: 0.0.1
;; Package-Requires: ((emacs "30"))

;; This file is not part of GNU Emacs.

;; This program is free software: you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <https://www.gnu.org/licenses/>.

;;; Commentary:

;;; Code:

(require 'elisp-mode)
(static-if (<= 31 emacs-major-version)
    (require 'elisp-scope))
(eval-when-compile
  (require 'cl-lib))

(defgroup incomplete nil
  "Better completion."
  :group 'lisp
  :prefix "incomplete-")

(cl-defgeneric incomplete--local-variables-1 (vars sexp))

(cl-defmethod incomplete--local-variables-1 :around (vars sexp)
  (if (and (consp sexp)
           (symbolp (car sexp))
           (static-if (<= 31 emacs-major-version)
               (elisp-scope-safe-macro-p (car sexp))
             (get (car sexp) 'safe-macro)))
      (condition-case _err
          (incomplete--local-variables-1
           vars
           (dlet ((inhibit-message t)
                  (macroexp-inhibit-compiler-macros t)
                  (warning-minimum-log-level :emergency))
             (macroexpand-1 sexp)))
        (error (cl-call-next-method)))
    (cl-call-next-method)))

;; From `elisp--local-variables-1'
(cl-defmethod incomplete--local-variables-1 (vars sexp)
  "Return VARS locally bound around the witness, or nil if not found."
  (let (res)
    (while
        (unless
            (setq res
                  (pcase sexp
                    (`(,(or 'let 'let*) ,bindings)
                     (let ((vars vars))
                       (when (eq 'let* (car sexp))
                         (dolist (binding (cdr (reverse bindings)))
                           (push (or (car-safe binding) binding) vars)))
                       (incomplete--local-variables-1
                        vars (car (cdr-safe (car (last bindings)))))))
                    (`(,(or 'let 'let*) ,bindings . ,body)
                     (let ((vars vars))
                       (dolist (binding bindings)
                         (push (or (car-safe binding) binding) vars))
                       (incomplete--local-variables-1 vars (car (last body)))))
                    (`(lambda ,_args)
                     ;; FIXME: Look for the witness inside `args'.
                     (setq sexp nil))
                    (`(lambda ,args . ,body)
                     (incomplete--local-variables-1
                      (let ((args (if (listp args) args)))
                        ;; FIXME: Exit the loop if witness is in args.
                        (append (remq '&optional (remq '&rest args)) vars))
                      (car (last body))))
                    (`(condition-case ,_ ,e) (incomplete--local-variables-1 vars e))
                    (`(condition-case ,v ,_ . ,catches)
                     (incomplete--local-variables-1
                      (cons v vars) (cdr (car (last catches)))))
                    (`(quote . ,_)
                     ;; FIXME: Look for the witness inside sexp.
                     (setq sexp nil))
                    (`(,(or 'with-slots 'cl-with-accessors)
                       ,spec-list ,_obj . ,body)
                     (incomplete--local-variables-1 vars `(let ,spec-list ,@body)))
                    (`(,(or 'dlet 'cl-symbol-macrolet) . ,_)
                     (incomplete--local-variables-1 vars (cons 'let (cdr sexp))))
                    (`(,(or 'when-let* 'and-let* 'while-let) . ,_)
                     (incomplete--local-variables-1 vars (cons 'let* (cdr sexp))))
                    (`(if-let* ,bindings ,then . ,else)
                     (or (incomplete--local-variables-1 vars `(let* ,bindings ,then))
                         (incomplete--local-variables-1 vars `(progn ,@else))))
                    (`(cl-letf ,bindings . ,body)
                     (incomplete--local-variables-1
                      vars `(let ,(seq-filter (lambda (b) (symbolp (car b))) bindings)
                              ,@body)))
                    (`(cl-letf* ,bindings . ,body)
                     (incomplete--local-variables-1
                      vars `(let* ,(seq-filter (lambda (b) (symbolp (car b))) bindings)
                              ,@body)))
                    (`(letrec ,bindings . ,body)
                     (let (lvars exps)
                       (pcase-dolist (`(,var ,exp) bindings)
                         (push var lvars)
                         (push exp exps))
                       (incomplete--local-variables-1 vars `(let ,lvars
                                                              ,@exps
                                                              ,@body))))
                    ;; FIXME: Handle `cond'.
                    (`(,_ . ,_)
                     (incomplete--local-variables-1 vars (car (last sexp))))
                    ('elisp--witness--lisp (or vars '(nil)))
                    (_ nil)))
          ;; We didn't find the witness in the last element so we try to
          ;; backtrack to the last-but-one.
          (setq sexp (ignore-errors (butlast sexp)))))
    res))

(defun incomplete--walk-pcase-pat (vars pat)
  (let ((pat (pcase--macroexpand pat))
        (pvars nil))
    (cl-labels ((walk (pat)
                  (pcase pat
                    (`(,(and (pred (get _ 'incomplete-safe-pcase-macro))
                             (app pcase--get-macroexpander
                                  (and expander (pred identity))))
                       . ,body)
                     (walk (apply expander body)))
                    (`(,(or 'pred 'guard 'quote) . ,_))
                    (`(,(or 'and 'or) . ,pats)
                     (mapc #'walk pats))
                    (`(app ,_ ,pat)
                     (walk pat))
                    (`(,(pred pcase--get-macroexpander) . ,rest)
                     (mapc #'walk rest))
                    ('elisp--witness--lisp
                     (throw 'pcase-return
                            (nconc pvars vars)))
                    ((pred symbolp)
                     (push pat pvars)))))
      (walk pat))
    pvars))

(cl-defmethod incomplete--local-variables-1 :extra "pcase" (vars sexp)
  (catch 'pcase-return
    (pcase sexp
      (`(pcase ,form . ,cases)
       (or (incomplete--local-variables-1 vars form)
           (pcase-dolist (`(,pat . ,body) (reverse cases))
             (let ((pvars (incomplete--walk-pcase-pat vars pat)))
               (when-let* ((res (incomplete--local-variables-1
                                 vars `(progn ,@body))))
                 (throw 'pcase-return (nconc pvars res)))))))
      (`(pcase-let ,bindings . ,body)
       (let ((pat-vars nil))
         (pcase-dolist (`(,pat ,exp) bindings)
           (let ((pvars (incomplete--walk-pcase-pat vars pat)))
             (when-let* ((res (incomplete--local-variables-1 vars exp)))
               (throw 'pcase-return res))
             (cl-callf2 nconc pvars pat-vars)))
         (incomplete--local-variables-1
          (nconc pat-vars vars)
          `(progn ,@body))))
      (`(pcase-let* ,bindings . ,body)
       (pcase-dolist (`(,pat ,exp) bindings)
         (let ((pvars (incomplete--walk-pcase-pat vars pat)))
           (when-let* ((res (incomplete--local-variables-1 vars exp)))
             (throw 'pcase-return res))
           (cl-callf2 nconc pvars vars)))
       (incomplete--local-variables-1
        vars `(progn ,@body)))
      (`(pcase-lambda ,arglist . ,body)
       (incomplete--local-variables-1
        (nconc (mapcan (lambda (p) (incomplete--walk-pcase-pat vars p))
                       arglist)
               vars)
        `(progn ,@body)))
      (`(pcase-dolist (,pat ,exp) . ,body)
       (let ((pvars (incomplete--walk-pcase-pat vars pat)))
         (or (incomplete--local-variables-1 vars exp)
             (incomplete--local-variables-1 (nconc pvars vars)
                                            `(progn ,@body)))))
      (_ (cl-call-next-method)))))

;; From `elisp--local-variables'
(defun incomplete--local-variables (extract kind)
  (save-excursion
    (skip-syntax-backward "w_")
    (let* ((ppss (syntax-ppss))
           (txt (buffer-substring-no-properties (or (car (nth 9 ppss)) (point))
                                                (or (nth 8 ppss) (point))))
           (closer ()))
      (dolist (p (nth 9 ppss))
        (push (cdr (syntax-after p)) closer))
      (setq closer (apply #'string closer))
      (let* ((sexp (condition-case nil
                       (car (read-from-string
                             (concat txt "elisp--witness--lisp" closer)))
                     ((invalid-read-syntax end-of-file) nil)))
             (vars (funcall extract nil sexp)))
        (delete-dups
         (delq nil
               (mapcar (lambda (var)
                         (and (symbolp var)
                              (not (string-match (symbol-name var) "\\`[&_]"))
                              ;; Eliminate uninterned vars.
                              (intern-soft var)
                              (propertize (symbol-name var)
                                          'kind (or kind 'text))))
                       vars)))))))

;; From `elisp--local-variables-completion-table'
(defconst incomplete--local-variables-completion-table
  (let ((lastpos nil)
        (lastvars nil)
        (hook-sym (make-symbol "hook")))
    (fset hook-sym (lambda ()
                     (setq lastpos nil)
                     (remove-hook 'post-command-hook hook-sym)))
    (completion-table-dynamic
     (lambda (_string)
       (save-excursion
         (skip-syntax-backward "_w")
         (let ((newpos (cons (point) (current-buffer))))
           (unless (equal lastpos newpos)
             (add-hook 'post-command-hook hook-sym)
             (setq lastpos newpos)
             (setq lastvars (incomplete--local-variables
                             #'incomplete--local-variables-1
                             'variable)))))
       lastvars))))

(cl-defgeneric incomplete--local-functions-1 (vars sexp))

(cl-defmethod incomplete--local-functions-1 (vars sexp)
  (let (res)
    (while
        (unless
            (setq res
                  (pcase sexp
                    (`(,(or 'let 'let*) ,bindings)
                     (incomplete--local-functions-1
                      vars (car (cdr-safe (car (last bindings))))))
                    (`(,(or 'let 'let*) ,_bindings . ,body)
                     (incomplete--local-functions-1 vars (car (last body))))
                    (`(lambda ,_args)
                     ;; FIXME: Look for the witness inside `args'.
                     (setq sexp nil))
                    (`(lambda ,_args . ,body)
                     (incomplete--local-functions-1 vars (car (last body))))
                    (`(condition-case ,_ ,e)
                     (incomplete--local-functions-1 vars e))
                    (`(condition-case ,_ ,_ . ,catches)
                     (incomplete--local-functions-1
                      vars (cdr (car (last catches)))))
                    (`(quote . ,_)
                     ;; FIXME: Look for the witness inside sexp.
                     (setq sexp nil))
                    ;; FIXME: Handle `cond'.
                    (`(,_ . ,_)
                     (incomplete--local-functions-1 vars (car (last sexp))))
                    ('elisp--witness--lisp (or vars '(nil)))
                    (_ nil)))
          ;; We didn't find the witness in the last element so we try to
          ;; backtrack to the last-but-one.
          (setq sexp (ignore-errors (butlast sexp)))))
    res))

(cl-defmethod incomplete--local-functions-1 (vars
                                             (sexp (head cl-labels)))
  (pcase sexp
    (`(,_ ,fbindings . ,body)
     (let* ((fbodies nil))
       (incomplete--local-functions-1
        (nconc (mapcar #'car fbindings)
               vars)
        `(progn ,@fbodies ,@body))))))

(cl-defmethod incomplete--local-functions-1 (vars
                                             (sexp (head cl-flet)))
  (incomplete--local-functions-1
   (nconc (mapcar #'car (cadr sexp))
          vars)
   `(progn ,@(cddr sexp))))

(defconst incomplete--local-functions-completion-table
  (let ((lastpos nil)
        (lastvars nil)
        (hook-sym (make-symbol "hook")))
    (fset hook-sym (lambda ()
                     (setq lastpos nil)
                     (remove-hook 'post-command-hook hook-sym)))
    (completion-table-dynamic
     (lambda (_string)
       (save-excursion
         (skip-syntax-backward "_w")
         (let ((newpos (cons (point) (current-buffer))))
           (unless (equal lastpos newpos)
             (add-hook 'post-command-hook hook-sym)
             (setq lastpos newpos)
             (setq lastvars (incomplete--local-variables
                             #'incomplete--local-functions-1
                             'function)))))
       lastvars))))

(defun incomplete--completion-local-symbols-advice (table)
  (let ((tables
         (list incomplete--local-functions-completion-table
               table)))
    (lambda (string pred action)
      (add-function :before-until (var pred)
                    (lambda (val) (stringp val)))
      (cond
       ((null action)
        (let ((retvals (mapcar (lambda (table)
                                 (try-completion string table pred))
                               tables)))
          (if (member string retvals)
              string
            (try-completion string
                            (mapcar (lambda (value)
                                      (if (eq value t) string value))
                                    (delq nil retvals))
                            pred))))
       ((eq action t)
        (apply #'append (mapcar (lambda (table)
                                  (all-completions string table pred))
                                tables)))
       (t
        (seq-some (lambda (table)
                    (complete-with-action action table string pred))
                  tables))))))

(defun incomplete--completion-advice (orig-fn)
  (let ((result
         (cl-letf (((symbol-function 'elisp--completion-local-symbols))
                   (elisp--local-variables-completion-table
                    incomplete--local-variables-completion-table))
           (advice-add 'elisp--completion-local-symbols :filter-return
                       #'incomplete--completion-local-symbols-advice)
           (funcall orig-fn))))
    (if (and result (listp result) (>= (length result) 3))
        (let ((plist (drop 3 result))
              (pred
               (lambda (str)
                 (and (stringp str)
                      (get-text-property 0 'kind str))))
              (sort
               (lambda (cands)
                 (let ((seen (make-hash-table :test #'equal))
                       local other)
                   (dolist (c cands)
                     (unless (gethash c seen)
                       (puthash c t seen)
                       (if (get-text-property 0 'kind c)
                           (push c local)
                         (push c other))))
                   (nconc (nreverse local) (nreverse other))))))
          (if (plist-get plist :predicate)
              (add-function :before-until
                            (plist-get plist :predicate)
                            pred)
            (setf (plist-get plist :predicate) pred))
          (if (plist-get plist :company-kind)
              (add-function :before-until
                            (plist-get plist :company-kind)
                            pred)
            (setf (plist-get plist :company-kind) pred))
          (if (plist-get plist :display-sort-function)
              (add-function :filter-return
                            (plist-get plist :display-sort-function)
                            sort)
            (setf (plist-get plist :display-sort-function) sort))
          (append (take 3 result) plist))
      result)))

(dolist (macro '(cl-loop
                 cl-defun
                 cl-defmacro
                 cl-defsubst
                 cl-defmethod
                 cl-defgeneric
                 cl-function
                 cl-do
                 cl-do*
                 dolist
                 define-inline
                 letrec
                 named-let
                 cl-letf
                 cl-letf*
                 defun
                 defmacro
                 when
                 unless))
  (function-put macro 'safe-macro t))

(dolist (macro '(map
                 cl-struct
                 eieio
                 seq
                 let
                 cl-type
                 radix-tree-leaf))
  (put macro 'incomplete-safe-pcase-macro t))

;;;###autoload
(define-minor-mode incomplete-mode
  "Better completions."
  :lighter nil
  :global t
  (if incomplete-mode
      (advice-add 'elisp-completion-at-point :around
                  #'incomplete--completion-advice)
    (advice-remove 'elisp-completion-at-point
                   #'incomplete--completion-advice)))

(provide 'incomplete)
