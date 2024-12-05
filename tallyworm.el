;; TODO: Rationalize the language here, by clarifying the status
;;       of 'spiral', 'grid', and 'canvas' coordinate systems,
;;       including the question of their separate existence(s).

;; There is a single transformation that carries each unit vector
;; to the next-higher dose: a +45° rotation followed by *√2 scaling.
;; On an integer grid, this is easily done without floating-point
;; arithmetic, since it's equivalent to adding a +90°-rotated copy.
(defun rot90 (xy) (pcase xy (`[,x ,y] (vector (- y) x))))
(rot90 [0 1]) ; => [-1 0]
(defun vec+ (v1 v2) (vconcat (seq-mapn #'+ v1 v2)))
(vec+ [0 1] [1 0]) ; => [1 1]
(defun spiral-next (xy) (vec+ xy (rot90 xy)))
(spiral-next (spiral-next [1 0])) ; => [0 2]

;; We obtain the radial and angular 'unit vectors' by recursion:
(defun radial-unit (d)
  "Spiral coordinates radial unit vector for dose-d tallies"
  (if (= d 1) [1 0]
    (spiral-next (radial-unit (- d 1)))))

(seq-map 'radial-unit '(1 2 3 4))
;; => ([1 0] [1 1] [0 2] [-2 2])

;; Should I call these rather _grid_ coordinates?
;; Or should we consider 'spiral coordinates' as *referred to* the grid?
(defun spiral-coords (q d)
  "Return the spiral coordinates of tally T/N at dose d0+1"
  (pcase q (`[,T ,N]
            (let* ((r (radial-unit d))
                   (a (rot90 r))
                   (U (- N T)))
              (coords-basis N U r a)))))

;; A problem here is that this does not respect a natural
;; construction of tallies via functor '/'.  Should I use
;; specialized *record*-type structures?

(defun coords-basis (x y u1 u2)
  "The 2-vector with basis-<u1,u2> coordinates [x y]"
  (vec+ (scalar* x u1) (scalar* y u2)))

(defun scalar* (s v) "Multiply vector v by scalar s"
       (vconcat (seq-map (apply-partially #'* s) v)))

(spiral-coords [1 2] 2) ; => [1 3]

;; Next, we need a way to convert a whole tally
;; to a list (or vector?) of spiral coordinates.
(defun tally-worm (tally)
  "Return a list of coordinates for 'worm' representation"
  (cdr (seq-map-indexed 'spiral-coords (cons nil tally))))

(spiral-coords [1 6] 1)
(spiral-coords [0 3] 2)
(spiral-coords [2 6] 3)
(spiral-coords nil 0)
(cdr (seq-map-indexed 'spiral-coords (list nil [1 6] [0 3] [2 6])))

(tally-worm (list [1 6] [0 3] [2 6]))
;; => ([6 5] [0 6] [-8 12])

;; Let us represent the |Qf|=29 final tallies of the D=2 3+3 trial:
(setq Q2f '(([0 3] [0 6] 2) ([0 3] [1 6] 2) ([1 6] [0 6] 2) ([1 6] [1 6] 2)
            ([0 6] [2 3] 1) ([0 6] [2 6] 1) ([0 6] [3 3] 1) ([0 6] [3 6] 1)
            ([0 6] [4 6] 1) ([1 6] [2 3] 1) ([1 6] [2 6] 1) ([1 6] [3 3] 1)
            ([1 6] [3 6] 1) ([1 6] [4 6] 1)
            ([2 3] [0 0] 0) ([2 6] [0 0] 0) ([2 6] [2 3] 0) ([2 6] [2 6] 0)
            ([2 6] [3 3] 0) ([2 6] [3 6] 0) ([2 6] [4 6] 0) ([3 3] [0 0] 0)
            ([3 6] [0 0] 0) ([3 6] [2 3] 0) ([3 6] [2 6] 0) ([3 6] [3 3] 0)
            ([3 6] [3 6] 0) ([3 6] [4 6] 0) ([4 6] [0 0] 0)
            ))
;; (NB: These are not rectified!)

;; The final step needed before we can really _plot_ points
;; is to define mapping of our natural grid to SVG canvas.

;; (It could be interesting to use local variables to shadow
;; default mappings defined globally.)

(defun range (m n)
  (if (= m n)
      (list n)
    (cons m (range (+ 1 m) n))))

(range 1 10)

(setq width 300)
(setq height 400)

;; I do need one more step below, namely flipping the y coordinate!
(defun vec* (v1 v2) (vconcat (seq-mapn #'* v1 v2)))
(defun flip (xy) (vec+ (vector 0 height) (vec* [1 -1] xy)))

`[0 ,height]      ; too cute
(vector 0 height) ; less cute, but somehow clearer!

(defun canvas (xy)
  "Return canvas coordinates for grid coordinates [x y]"
  (let ((margin [10 10])
        (scale 20))
    (flip (vec+ margin (scalar* scale xy)))))

(canvas [1 1])

(setq svg (svg-create width height :stroke "black" :stroke-width 2))
(save-excursion (goto-char (point-max)) (svg-insert-image svg))

;; I need a basic function to draw the grid dots at vector coordinates
(defun dot (xy)
  "Draw a dot at grid coordinates [x y]"
  (pcase-let ((`[,x ,y] xy)
              (radius 3))
    (svg-circle svg x y radius :stroke "lightgray" :fill "lightgray")))

(defun dots (d)
  "Plot grid for dose level d"
  (seq-map (lambda (N)
             (seq-map (lambda (T)
                        (dot (canvas (spiral-coords (vector T N) d))))
                      (range 0 N)))
           (range 0 6)))

(dots 1)
(dots 2)



