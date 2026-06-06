package com.example.georeminderl2

import android.Manifest
import android.annotation.SuppressLint
import android.app.NotificationChannel
import android.app.NotificationManager
import android.app.PendingIntent
import android.content.Context
import android.content.Intent
import android.content.pm.PackageManager
import android.graphics.Color
import android.location.Location
import android.os.Build
import android.os.Bundle
import android.os.Looper
import android.os.SystemClock
import android.os.VibrationEffect
import android.os.Vibrator
import android.os.VibratorManager
import android.text.InputType
import android.view.MotionEvent
import android.view.View
import android.view.inputmethod.InputMethodManager
import android.widget.Button
import android.widget.EditText
import android.widget.LinearLayout
import android.widget.TextView
import android.widget.Toast
import androidx.activity.result.contract.ActivityResultContracts
import androidx.appcompat.app.AlertDialog
import androidx.appcompat.app.AppCompatActivity
import androidx.core.app.NotificationCompat
import androidx.core.app.NotificationManagerCompat
import androidx.core.content.ContextCompat
import com.google.android.gms.location.FusedLocationProviderClient
import com.google.android.gms.location.LocationCallback
import com.google.android.gms.location.LocationRequest
import com.google.android.gms.location.LocationResult
import com.google.android.gms.location.LocationServices
import com.google.android.gms.location.Priority
import okhttp3.Call
import okhttp3.Callback as OkHttpCallback
import okhttp3.OkHttpClient
import okhttp3.Request
import okhttp3.Response
import org.json.JSONArray
import org.json.JSONObject
import org.osmdroid.config.Configuration
import org.osmdroid.events.MapEventsReceiver
import org.osmdroid.tileprovider.tilesource.TileSourceFactory
import org.osmdroid.util.BoundingBox
import org.osmdroid.util.GeoPoint
import org.osmdroid.views.MapView
import org.osmdroid.views.overlay.MapEventsOverlay
import org.osmdroid.views.overlay.Marker
import org.osmdroid.views.overlay.Overlay
import org.osmdroid.views.overlay.Polygon
import org.osmdroid.views.overlay.Polyline
import java.io.IOException
import java.util.Locale
import kotlin.math.abs
import kotlin.math.min

class MainActivity : AppCompatActivity() {

    companion object {
        private const val CHANNEL_ID = "geo_reminder_channel"
        private const val BASE_NOTIFICATION_ID = 2000

        private const val LOCATION_UPDATE_INTERVAL_MS = 4000L
        private const val LOCATION_FASTEST_INTERVAL_MS = 2000L
        private const val LOCATION_MIN_DISTANCE_METERS = 2f

        private const val PREFS_NAME = "geo_reminder_storage"
        private const val KEY_REMINDERS = "saved_reminders"
        private const val KEY_NEXT_ID = "next_reminder_id"
    }

    private lateinit var mapView: MapView

    private lateinit var bottomSheet: LinearLayout
    private lateinit var bottomHandle: View
    private lateinit var bottomSheetContent: LinearLayout

    private lateinit var tvStatus: TextView
    private lateinit var tvDistance: TextView
    private lateinit var tvSpeed: TextView
    private lateinit var tvPoints: TextView
    private lateinit var tvReminder: TextView

    private lateinit var btnMyLocation: Button
    private lateinit var btnToggleAllRadii: Button
    private lateinit var btnTrash: Button
    private lateinit var btnStartTrack: Button
    private lateinit var btnStopTrack: Button
    private lateinit var btnClearRouteTrack: Button

    private lateinit var fusedLocationClient: FusedLocationProviderClient
    private lateinit var locationRequest: LocationRequest
    private lateinit var locationCallback: LocationCallback

    private val httpClient = OkHttpClient()

    private var locationUpdatesStarted = false
    private var mapCenteredOnUser = false

    private var currentPoint: GeoPoint? = null
    private var userMarker: Marker? = null

    private var routeLine: Polyline? = null

    private var isTracking = false
    private val trackPoints = mutableListOf<GeoPoint>()
    private var trackLine: Polyline? = null
    private var trackStartTimeMs = 0L
    private var trackDistanceMeters = 0f

    private var bottomSheetCollapsed = false
    private var allRadiiVisible = false

    private var selectionMode = false
    private val selectedForDeleteIds = mutableSetOf<Int>()

    private var areaDeleteMode = false
    private val areaCorners = mutableListOf<GeoPoint>()
    private var areaDeletePolygon: Polygon? = null

    private val reminders = mutableListOf<GeoReminder>()
    private var selectedReminder: GeoReminder? = null
    private var nextReminderId = 1

    private val defaultMapCenter = GeoPoint(54.735147, 55.958727)

    private data class GeoReminder(
        val id: Int,
        var title: String,
        var message: String,
        var radiusMeters: Double,
        val point: GeoPoint,
        val marker: Marker,
        val circle: Polygon,
        var triggered: Boolean = false
    )

    private data class RouteResult(
        val points: List<GeoPoint>,
        val distanceMeters: Double,
        val durationSeconds: Double
    )

    private val permissionLauncher =
        registerForActivityResult(ActivityResultContracts.RequestMultiplePermissions()) { result ->
            val fineGranted = result[Manifest.permission.ACCESS_FINE_LOCATION] == true
            val coarseGranted = result[Manifest.permission.ACCESS_COARSE_LOCATION] == true

            if (fineGranted || coarseGranted) {
                updateStatus("GPS работает")
                startLocationUpdates()
            } else {
                updateStatus("Нет разрешения на геолокацию")
                Toast.makeText(
                    this,
                    "Без геолокации карта, маршрут и напоминания работать не будут",
                    Toast.LENGTH_LONG
                ).show()
            }
        }

    override fun onCreate(savedInstanceState: Bundle?) {
        super.onCreate(savedInstanceState)

        Configuration.getInstance().userAgentValue = packageName
        Configuration.getInstance().load(
            applicationContext,
            getSharedPreferences("osmdroid_settings", MODE_PRIVATE)
        )

        setContentView(R.layout.activity_main)

        initViews()
        createNotificationChannel()
        setupMap()
        setupLocation()
        setupButtons()
        setupBottomSheet()
        updateTrackStats()

        loadRemindersFromStorage()

        requestNeededPermissions()
    }

    override fun onResume() {
        super.onResume()
        mapView.onResume()

        if (hasLocationPermission()) {
            startLocationUpdates()
        }
    }

    override fun onPause() {
        super.onPause()
        mapView.onPause()
        stopLocationUpdates()
        saveRemindersToStorage()
    }

    override fun onDestroy() {
        super.onDestroy()
        stopLocationUpdates()
        saveRemindersToStorage()
    }

    private fun initViews() {
        mapView = findViewById(R.id.mapView)

        bottomSheet = findViewById(R.id.bottomSheet)
        bottomHandle = findViewById(R.id.bottomHandle)
        bottomSheetContent = findViewById(R.id.bottomSheetContent)

        tvStatus = findViewById(R.id.tvStatus)
        tvDistance = findViewById(R.id.tvDistance)
        tvSpeed = findViewById(R.id.tvSpeed)
        tvPoints = findViewById(R.id.tvPoints)
        tvReminder = findViewById(R.id.tvReminder)

        btnMyLocation = findViewById(R.id.btnMyLocation)
        btnToggleAllRadii = findViewById(R.id.btnToggleAllRadii)
        btnTrash = findViewById(R.id.btnTrash)
        btnStartTrack = findViewById(R.id.btnStartTrack)
        btnStopTrack = findViewById(R.id.btnStopTrack)
        btnClearRouteTrack = findViewById(R.id.btnClearRouteTrack)
    }

    private fun setupMap() {
        mapView.setTileSource(TileSourceFactory.MAPNIK)
        mapView.setMultiTouchControls(true)
        mapView.controller.setZoom(15.5)
        mapView.controller.setCenter(defaultMapCenter)

        val receiver = object : MapEventsReceiver {
            override fun singleTapConfirmedHelper(p: GeoPoint?): Boolean {
                if (p != null && areaDeleteMode) {
                    handleAreaDeletePoint(p)
                    return true
                }

                return false
            }

            override fun longPressHelper(p: GeoPoint?): Boolean {
                if (p == null) {
                    return false
                }

                if (areaDeleteMode) {
                    handleAreaDeletePoint(p)
                    return true
                }

                if (selectionMode) {
                    Toast.makeText(
                        this@MainActivity,
                        "Сейчас режим выбора меток. Нажимай по меткам.",
                        Toast.LENGTH_SHORT
                    ).show()
                    return true
                }

                showCreateReminderDialog(p)
                return true
            }
        }

        mapView.overlays.add(MapEventsOverlay(receiver))
        updateStatus("Зажми карту, чтобы создать метку")
    }

    private fun setupLocation() {
        fusedLocationClient = LocationServices.getFusedLocationProviderClient(this)

        locationRequest = LocationRequest.Builder(
            Priority.PRIORITY_HIGH_ACCURACY,
            LOCATION_UPDATE_INTERVAL_MS
        )
            .setMinUpdateIntervalMillis(LOCATION_FASTEST_INTERVAL_MS)
            .setMinUpdateDistanceMeters(LOCATION_MIN_DISTANCE_METERS)
            .build()

        locationCallback = object : LocationCallback() {
            override fun onLocationResult(locationResult: LocationResult) {
                for (location in locationResult.locations) {
                    handleNewLocation(location)
                }
            }
        }
    }

    private fun setupButtons() {
        btnMyLocation.setOnClickListener {
            moveToMyLocation()
        }

        btnToggleAllRadii.setOnClickListener {
            toggleAllRadii()
        }

        btnTrash.setOnClickListener {
            showTrashMenu()
        }

        btnStartTrack.setOnClickListener {
            startTrack()
        }

        btnStopTrack.setOnClickListener {
            stopTrack()
        }

        btnClearRouteTrack.setOnClickListener {
            clearRouteAndTrack()
        }
    }

    @SuppressLint("ClickableViewAccessibility")
    private fun setupBottomSheet() {
        expandBottomSheet()

        var startRawY = 0f

        bottomHandle.setOnTouchListener { _, event ->
            when (event.action) {
                MotionEvent.ACTION_DOWN -> {
                    startRawY = event.rawY
                    true
                }

                MotionEvent.ACTION_UP, MotionEvent.ACTION_CANCEL -> {
                    val dy = event.rawY - startRawY

                    when {
                        abs(dy) < 25f -> toggleBottomSheet()
                        dy > 25f -> collapseBottomSheet()
                        dy < -25f -> expandBottomSheet()
                    }

                    true
                }

                else -> true
            }
        }
    }

    private fun toggleBottomSheet() {
        if (bottomSheetCollapsed) {
            expandBottomSheet()
        } else {
            collapseBottomSheet()
        }
    }

    private fun collapseBottomSheet() {
        bottomSheetCollapsed = true

        bottomSheetContent.animate()
            .alpha(0f)
            .setDuration(130)
            .withEndAction {
                bottomSheetContent.visibility = View.GONE
            }
            .start()
    }

    private fun expandBottomSheet() {
        bottomSheetCollapsed = false

        bottomSheetContent.visibility = View.VISIBLE
        bottomSheetContent.alpha = 0f

        bottomSheetContent.animate()
            .alpha(1f)
            .setDuration(130)
            .start()
    }

    private fun requestNeededPermissions() {
        val permissions = mutableListOf(
            Manifest.permission.ACCESS_FINE_LOCATION,
            Manifest.permission.ACCESS_COARSE_LOCATION
        )

        if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.TIRAMISU) {
            permissions.add(Manifest.permission.POST_NOTIFICATIONS)
        }

        permissionLauncher.launch(permissions.toTypedArray())
    }

    private fun hasLocationPermission(): Boolean {
        val fineGranted = ContextCompat.checkSelfPermission(
            this,
            Manifest.permission.ACCESS_FINE_LOCATION
        ) == PackageManager.PERMISSION_GRANTED

        val coarseGranted = ContextCompat.checkSelfPermission(
            this,
            Manifest.permission.ACCESS_COARSE_LOCATION
        ) == PackageManager.PERMISSION_GRANTED

        return fineGranted || coarseGranted
    }

    private fun hasNotificationPermission(): Boolean {
        return Build.VERSION.SDK_INT < Build.VERSION_CODES.TIRAMISU ||
                ContextCompat.checkSelfPermission(
                    this,
                    Manifest.permission.POST_NOTIFICATIONS
                ) == PackageManager.PERMISSION_GRANTED
    }

    @SuppressLint("MissingPermission")
    private fun startLocationUpdates() {
        if (!hasLocationPermission()) {
            requestNeededPermissions()
            return
        }

        if (locationUpdatesStarted) {
            return
        }

        locationUpdatesStarted = true

        fusedLocationClient.requestLocationUpdates(
            locationRequest,
            locationCallback,
            Looper.getMainLooper()
        )

        fusedLocationClient.lastLocation.addOnSuccessListener { location ->
            if (location != null) {
                handleNewLocation(location)
            }
        }

        updateStatus("GPS активен")
    }

    private fun stopLocationUpdates() {
        if (!locationUpdatesStarted) {
            return
        }

        fusedLocationClient.removeLocationUpdates(locationCallback)
        locationUpdatesStarted = false
    }

    private fun handleNewLocation(location: Location) {
        val point = GeoPoint(location.latitude, location.longitude)
        currentPoint = point

        updateUserMarker(point)

        if (!mapCenteredOnUser) {
            mapCenteredOnUser = true
            mapView.controller.setZoom(17.0)
            mapView.controller.animateTo(point)
        }

        if (isTracking) {
            addPointToTrack(point)
        }

        checkReminders(point)
        updateSelectedReminderText()
    }

    private fun updateUserMarker(point: GeoPoint) {
        if (userMarker == null) {
            userMarker = Marker(mapView).apply {
                icon = ContextCompat.getDrawable(this@MainActivity, R.drawable.ic_my_location)
                setTitle("")
                setSnippet("")
                setAnchor(Marker.ANCHOR_CENTER, Marker.ANCHOR_CENTER)
                setOnMarkerClickListener { _, _ ->
                    mapView.controller.animateTo(point)
                    true
                }
            }
            mapView.overlays.add(userMarker)
        }

        userMarker?.position = point
        mapView.invalidate()
    }

    private fun moveToMyLocation() {
        val point = currentPoint

        if (point == null) {
            Toast.makeText(this, "GPS ещё не определил местоположение", Toast.LENGTH_SHORT).show()
            updateStatus("Ожидаю GPS")
            return
        }

        mapView.controller.setZoom(18.0)
        mapView.controller.animateTo(point)
        updateStatus("Карта перемещена к вам")
    }

    private fun showCreateReminderDialog(point: GeoPoint) {
        hideKeyboard()

        val container = LinearLayout(this).apply {
            orientation = LinearLayout.VERTICAL
            setPadding(42, 10, 42, 0)
        }

        val titleInput = EditText(this).apply {
            hint = "Название метки"
            setText("")
            setSingleLine(true)
        }

        val messageInput = EditText(this).apply {
            hint = "Текст напоминания"
            setText("")
            minLines = 2
            maxLines = 3
        }

        val radiusInput = EditText(this).apply {
            hint = "Радиус, м"
            setText("")
            inputType = InputType.TYPE_CLASS_NUMBER or InputType.TYPE_NUMBER_FLAG_DECIMAL
            setSingleLine(true)
        }

        container.addView(titleInput)
        container.addView(messageInput)
        container.addView(radiusInput)

        AlertDialog.Builder(this)
            .setTitle("Новая метка")
            .setView(container)
            .setPositiveButton("Создать") { _, _ ->
                val title = titleInput.text.toString().trim().ifEmpty {
                    "Метка"
                }

                val message = messageInput.text.toString().trim().ifEmpty {
                    "Вы вошли в заданную зону"
                }

                val radius = radiusInput.text.toString().replace(",", ".").toDoubleOrNull()
                    ?.coerceIn(30.0, 5000.0)
                    ?: 200.0

                addReminder(
                    point = point,
                    title = title,
                    message = message,
                    radiusMeters = radius,
                    triggered = false,
                    idFromStorage = null,
                    saveAfterCreate = true
                )
            }
            .setNegativeButton("Отмена", null)
            .show()
    }

    private fun addReminder(
        point: GeoPoint,
        title: String,
        message: String,
        radiusMeters: Double,
        triggered: Boolean,
        idFromStorage: Int?,
        saveAfterCreate: Boolean
    ) {
        val circle = Polygon().apply {
            points = Polygon.pointsAsCircle(point, radiusMeters)
            fillPaint.color = Color.argb(45, 0, 166, 118)
            outlinePaint.color = Color.parseColor("#00A676")
            outlinePaint.strokeWidth = 5f
            setEnabled(false)
        }

        val marker = Marker(mapView).apply {
            position = point
            icon = ContextCompat.getDrawable(this@MainActivity, R.drawable.ic_reminder_pin)
            setTitle("")
            setSnippet("")
            setAnchor(Marker.ANCHOR_CENTER, Marker.ANCHOR_BOTTOM)
        }

        val reminderId = idFromStorage ?: nextReminderId++

        if (idFromStorage != null && idFromStorage >= nextReminderId) {
            nextReminderId = idFromStorage + 1
        }

        val reminder = GeoReminder(
            id = reminderId,
            title = title,
            message = message,
            radiusMeters = radiusMeters,
            point = point,
            marker = marker,
            circle = circle,
            triggered = triggered
        )

        marker.setOnMarkerClickListener { _, _ ->
            if (selectionMode) {
                toggleReminderSelection(reminder)
                true
            } else {
                selectedReminder = reminder
                updateSelectedReminderText()
                showReminderActionMenu(reminder)
                mapView.invalidate()
                true
            }
        }

        reminders.add(reminder)
        selectedReminder = reminder

        mapView.overlays.add(circle)
        mapView.overlays.add(marker)

        updateSelectedReminderText()
        updateStatus("Создана метка: $title")
        mapView.invalidate()

        if (saveAfterCreate) {
            saveRemindersToStorage()
        }

        currentPoint?.let { checkReminders(it) }
    }

    private fun showReminderActionMenu(reminder: GeoReminder) {
        selectedReminder = reminder
        updateSelectedReminderText()

        val actions = arrayOf(
            "Построить маршрут по дорогам",
            "Изменить радиус",
            "Удалить метку"
        )

        AlertDialog.Builder(this)
            .setTitle(reminder.title)
            .setItems(actions) { _, which ->
                when (which) {
                    0 -> buildRouteToReminder(reminder)
                    1 -> showEditRadiusDialog(reminder)
                    2 -> deleteReminder(reminder)
                }
            }
            .show()
    }

    private fun showEditRadiusDialog(reminder: GeoReminder) {
        val input = EditText(this).apply {
            hint = "Радиус, м"
            setText(reminder.radiusMeters.toInt().toString())
            inputType = InputType.TYPE_CLASS_NUMBER or InputType.TYPE_NUMBER_FLAG_DECIMAL
            setSingleLine(true)
        }

        AlertDialog.Builder(this)
            .setTitle("Изменить радиус")
            .setView(input)
            .setPositiveButton("Сохранить") { _, _ ->
                val newRadius = input.text.toString().replace(",", ".").toDoubleOrNull()
                    ?.coerceIn(30.0, 5000.0)
                    ?: reminder.radiusMeters

                reminder.radiusMeters = newRadius
                reminder.circle.points = Polygon.pointsAsCircle(reminder.point, newRadius)
                reminder.triggered = false

                updateSelectedReminderText()
                updateStatus("Радиус изменён: ${newRadius.toInt()} м")
                saveRemindersToStorage()
                mapView.invalidate()
            }
            .setNegativeButton("Отмена", null)
            .show()
    }

    private fun buildRouteToReminder(reminder: GeoReminder) {
        val start = currentPoint

        if (start == null) {
            Toast.makeText(this, "Сначала дождись GPS", Toast.LENGTH_LONG).show()
            updateStatus("Нет текущих координат")
            return
        }

        selectedReminder = reminder
        updateSelectedReminderText()

        buildRealRoadRoute(
            start = start,
            finish = reminder.point,
            routeName = "Маршрут к «${reminder.title}»"
        )
    }

    private fun deleteReminder(reminder: GeoReminder) {
        removeOverlay(reminder.marker)
        removeOverlay(reminder.circle)
        reminders.remove(reminder)
        selectedForDeleteIds.remove(reminder.id)

        if (selectedReminder == reminder) {
            selectedReminder = reminders.lastOrNull()
        }

        updateSelectedReminderText()
        updateStatus("Метка удалена")
        saveRemindersToStorage()
        mapView.invalidate()
    }

    private fun updateSelectedReminderText() {
        if (selectionMode) {
            tvReminder.text = "Выбор меток: выбрано ${selectedForDeleteIds.size}"
            return
        }

        if (areaDeleteMode) {
            tvReminder.text = "Удаление областью: выбери 2 угла области"
            return
        }

        val reminder = selectedReminder

        if (reminder == null) {
            tvReminder.text = "Зажми карту, чтобы создать метку"
            return
        }

        val distanceText = currentPoint?.let {
            formatDistance(distanceBetween(it, reminder.point).toDouble())
        } ?: "GPS ждёт координаты"

        tvReminder.text =
            "${reminder.title} · радиус ${reminder.radiusMeters.toInt()} м · до точки $distanceText"
    }

    private fun checkReminders(current: GeoPoint) {
        for (reminder in reminders) {
            if (reminder.triggered) {
                continue
            }

            val distance = distanceBetween(current, reminder.point)

            if (distance <= reminder.radiusMeters) {
                reminder.triggered = true
                selectedReminder = reminder
                reminder.circle.setEnabled(true)

                updateSelectedReminderText()
                updateStatus("Сработало: ${reminder.title}")

                showReminderNotification(reminder)
                vibrateOnce()
                saveRemindersToStorage()
                mapView.invalidate()
            }
        }
    }

    private fun buildRealRoadRoute(start: GeoPoint, finish: GeoPoint, routeName: String) {
        updateStatus("Строю маршрут по дорогам...")

        val url =
            "https://router.project-osrm.org/route/v1/driving/" +
                    "${start.longitude},${start.latitude};${finish.longitude},${finish.latitude}" +
                    "?overview=full&geometries=geojson&steps=false"

        val request = Request.Builder()
            .url(url)
            .get()
            .build()

        httpClient.newCall(request).enqueue(object : OkHttpCallback {
            override fun onFailure(call: Call, e: IOException) {
                runOnUiThread {
                    updateStatus("Маршрут не построен")
                    Toast.makeText(
                        this@MainActivity,
                        "Проверь интернет. Маршрут строится через OSRM.",
                        Toast.LENGTH_LONG
                    ).show()
                }
            }

            override fun onResponse(call: Call, response: Response) {
                try {
                    response.use { safeResponse ->
                        if (!safeResponse.isSuccessful) {
                            throw IOException("OSRM response code: ${safeResponse.code}")
                        }

                        val body = safeResponse.body?.string()
                            ?: throw IOException("Пустой ответ OSRM")

                        val routeResult = parseOsrmRoute(body)

                        runOnUiThread {
                            drawRoute(routeResult, routeName)
                        }
                    }
                } catch (e: Exception) {
                    runOnUiThread {
                        updateStatus("Маршрут для этих точек не найден")
                        Toast.makeText(
                            this@MainActivity,
                            "OSRM не смог построить маршрут для выбранных точек",
                            Toast.LENGTH_LONG
                        ).show()
                    }
                }
            }
        })
    }

    private fun parseOsrmRoute(jsonText: String): RouteResult {
        val root = JSONObject(jsonText)
        val routes = root.getJSONArray("routes")

        if (routes.length() == 0) {
            error("OSRM не вернул маршруты")
        }

        val route = routes.getJSONObject(0)

        val distanceMeters = route.getDouble("distance")
        val durationSeconds = route.getDouble("duration")

        val geometry = route.getJSONObject("geometry")
        val coordinates = geometry.getJSONArray("coordinates")

        val routePoints = mutableListOf<GeoPoint>()

        for (i in 0 until coordinates.length()) {
            val pair = coordinates.getJSONArray(i)

            val longitude = pair.getDouble(0)
            val latitude = pair.getDouble(1)

            routePoints.add(GeoPoint(latitude, longitude))
        }

        return RouteResult(
            points = routePoints,
            distanceMeters = distanceMeters,
            durationSeconds = durationSeconds
        )
    }

    private fun drawRoute(routeResult: RouteResult, routeName: String) {
        removeOverlay(routeLine)

        routeLine = Polyline().apply {
            setPoints(routeResult.points)
            outlinePaint.color = Color.parseColor("#C62828")
            outlinePaint.strokeWidth = 9f
        }

        mapView.overlays.add(routeLine)

        if (routeResult.points.isNotEmpty()) {
            val box = BoundingBox.fromGeoPoints(routeResult.points)
            mapView.zoomToBoundingBox(box, true, 120)
        }

        val durationMinutes = routeResult.durationSeconds / 60.0

        updateStatus(
            String.format(
                Locale.getDefault(),
                "%s · %s · %.0f мин",
                routeName,
                formatDistance(routeResult.distanceMeters),
                durationMinutes
            )
        )

        Toast.makeText(
            this,
            "Маршрут построен по реальным дорогам",
            Toast.LENGTH_SHORT
        ).show()

        mapView.invalidate()
    }

    private fun showTrashMenu() {
        val actions = if (selectionMode) {
            arrayOf(
                "Удалить выбранные метки (${selectedForDeleteIds.size})",
                "Отменить выбор",
                "Удалить по выделенной области",
                "Удалить все метки"
            )
        } else {
            arrayOf(
                "Выбрать метки",
                "Удалить по выделенной области",
                "Удалить все метки"
            )
        }

        AlertDialog.Builder(this)
            .setTitle("Метки")
            .setItems(actions) { _, which ->
                if (selectionMode) {
                    when (which) {
                        0 -> deleteSelectedMarkers()
                        1 -> stopSelectionMode()
                        2 -> startAreaDeleteMode()
                        3 -> deleteAllMarkers()
                    }
                } else {
                    when (which) {
                        0 -> startSelectionMode()
                        1 -> startAreaDeleteMode()
                        2 -> deleteAllMarkers()
                    }
                }
            }
            .show()
    }

    private fun startSelectionMode() {
        if (reminders.isEmpty()) {
            Toast.makeText(this, "Меток пока нет", Toast.LENGTH_SHORT).show()
            return
        }

        areaDeleteMode = false
        removeOverlay(areaDeletePolygon)
        areaDeletePolygon = null
        areaCorners.clear()

        selectionMode = true
        selectedForDeleteIds.clear()

        for (reminder in reminders) {
            reminder.marker.icon = ContextCompat.getDrawable(this, R.drawable.ic_reminder_pin)
        }

        updateStatus("Режим выбора: нажимай на метки")
        updateSelectedReminderText()
        mapView.invalidate()
    }

    private fun stopSelectionMode() {
        selectionMode = false
        selectedForDeleteIds.clear()

        for (reminder in reminders) {
            reminder.marker.icon = ContextCompat.getDrawable(this, R.drawable.ic_reminder_pin)
        }

        updateStatus("Выбор отменён")
        updateSelectedReminderText()
        mapView.invalidate()
    }

    private fun toggleReminderSelection(reminder: GeoReminder) {
        if (selectedForDeleteIds.contains(reminder.id)) {
            selectedForDeleteIds.remove(reminder.id)
            reminder.marker.icon = ContextCompat.getDrawable(this, R.drawable.ic_reminder_pin)
        } else {
            selectedForDeleteIds.add(reminder.id)
            reminder.marker.icon = ContextCompat.getDrawable(this, R.drawable.ic_reminder_pin_selected)
        }

        updateStatus("Выбрано меток: ${selectedForDeleteIds.size}")
        updateSelectedReminderText()
        mapView.invalidate()
    }

    private fun deleteSelectedMarkers() {
        if (selectedForDeleteIds.isEmpty()) {
            Toast.makeText(this, "Ни одна метка не выбрана", Toast.LENGTH_SHORT).show()
            return
        }

        val toDelete = reminders.filter { selectedForDeleteIds.contains(it.id) }

        for (reminder in toDelete) {
            removeOverlay(reminder.marker)
            removeOverlay(reminder.circle)
        }

        reminders.removeAll(toDelete.toSet())
        selectedForDeleteIds.clear()
        selectionMode = false
        selectedReminder = reminders.lastOrNull()

        updateStatus("Удалено меток: ${toDelete.size}")
        updateSelectedReminderText()
        saveRemindersToStorage()
        mapView.invalidate()
    }

    private fun startAreaDeleteMode() {
        if (reminders.isEmpty()) {
            Toast.makeText(this, "Меток пока нет", Toast.LENGTH_SHORT).show()
            return
        }

        selectionMode = false
        selectedForDeleteIds.clear()

        for (reminder in reminders) {
            reminder.marker.icon = ContextCompat.getDrawable(this, R.drawable.ic_reminder_pin)
        }

        areaDeleteMode = true
        areaCorners.clear()

        removeOverlay(areaDeletePolygon)
        areaDeletePolygon = null

        updateStatus("Выбери 2 угла области на карте")
        updateSelectedReminderText()
        Toast.makeText(this, "Нажми на карте 2 точки — получится область удаления", Toast.LENGTH_LONG).show()
        mapView.invalidate()
    }

    private fun handleAreaDeletePoint(point: GeoPoint) {
        areaCorners.add(point)

        if (areaCorners.size == 1) {
            updateStatus("Первый угол выбран. Выбери второй угол.")
            Toast.makeText(this, "Теперь нажми второй угол области", Toast.LENGTH_SHORT).show()
            return
        }

        val first = areaCorners[0]
        val second = areaCorners[1]

        drawDeleteArea(first, second)

        val toDelete = reminders.filter { reminder ->
            isPointInsideRectangle(reminder.point, first, second)
        }

        AlertDialog.Builder(this)
            .setTitle("Удалить метки в области?")
            .setMessage("Найдено меток: ${toDelete.size}")
            .setPositiveButton("Удалить") { _, _ ->
                for (reminder in toDelete) {
                    removeOverlay(reminder.marker)
                    removeOverlay(reminder.circle)
                }

                reminders.removeAll(toDelete.toSet())

                if (selectedReminder != null && !reminders.contains(selectedReminder)) {
                    selectedReminder = reminders.lastOrNull()
                }

                saveRemindersToStorage()
                finishAreaDeleteMode("Удалено меток: ${toDelete.size}")
            }
            .setNegativeButton("Отмена") { _, _ ->
                finishAreaDeleteMode("Удаление областью отменено")
            }
            .show()
    }

    private fun drawDeleteArea(first: GeoPoint, second: GeoPoint) {
        removeOverlay(areaDeletePolygon)

        val minLat = min(first.latitude, second.latitude)
        val maxLat = kotlin.math.max(first.latitude, second.latitude)
        val minLon = min(first.longitude, second.longitude)
        val maxLon = kotlin.math.max(first.longitude, second.longitude)

        areaDeletePolygon = Polygon().apply {
            points = listOf(
                GeoPoint(minLat, minLon),
                GeoPoint(minLat, maxLon),
                GeoPoint(maxLat, maxLon),
                GeoPoint(maxLat, minLon),
                GeoPoint(minLat, minLon)
            )
            fillPaint.color = Color.argb(55, 198, 40, 40)
            outlinePaint.color = Color.parseColor("#C62828")
            outlinePaint.strokeWidth = 6f
            setEnabled(true)
        }

        mapView.overlays.add(areaDeletePolygon)
        mapView.invalidate()
    }

    private fun finishAreaDeleteMode(status: String) {
        areaDeleteMode = false
        areaCorners.clear()

        removeOverlay(areaDeletePolygon)
        areaDeletePolygon = null

        updateStatus(status)
        updateSelectedReminderText()
        mapView.invalidate()
    }

    private fun isPointInsideRectangle(point: GeoPoint, first: GeoPoint, second: GeoPoint): Boolean {
        val minLat = min(first.latitude, second.latitude)
        val maxLat = kotlin.math.max(first.latitude, second.latitude)
        val minLon = min(first.longitude, second.longitude)
        val maxLon = kotlin.math.max(first.longitude, second.longitude)

        return point.latitude in minLat..maxLat && point.longitude in minLon..maxLon
    }

    private fun deleteAllMarkers() {
        if (reminders.isEmpty()) {
            Toast.makeText(this, "Меток пока нет", Toast.LENGTH_SHORT).show()
            return
        }

        AlertDialog.Builder(this)
            .setTitle("Удалить все метки?")
            .setMessage("Будут удалены все созданные метки и их радиусы.")
            .setPositiveButton("Удалить всё") { _, _ ->
                for (reminder in reminders) {
                    removeOverlay(reminder.marker)
                    removeOverlay(reminder.circle)
                }

                reminders.clear()
                selectedReminder = null
                selectedForDeleteIds.clear()
                selectionMode = false

                saveRemindersToStorage()

                updateStatus("Все метки удалены")
                updateSelectedReminderText()
                mapView.invalidate()
            }
            .setNegativeButton("Отмена", null)
            .show()
    }

    private fun clearRouteAndTrack() {
        removeOverlay(routeLine)
        routeLine = null

        removeOverlay(trackLine)
        trackLine = null

        isTracking = false
        trackPoints.clear()
        trackDistanceMeters = 0f
        trackStartTimeMs = 0L

        updateTrackStats()
        updateStatus("Маршрут и трек очищены")
        mapView.invalidate()
    }

    private fun toggleAllRadii() {
        allRadiiVisible = !allRadiiVisible

        for (reminder in reminders) {
            reminder.circle.setEnabled(allRadiiVisible)
        }

        btnToggleAllRadii.text = if (allRadiiVisible) {
            "●"
        } else {
            "○"
        }

        updateStatus(
            if (allRadiiVisible) {
                "Радиусы показаны"
            } else {
                "Радиусы скрыты"
            }
        )

        mapView.invalidate()
    }

    private fun startTrack() {
        if (!hasLocationPermission()) {
            requestNeededPermissions()
            return
        }

        isTracking = true
        trackPoints.clear()
        trackDistanceMeters = 0f
        trackStartTimeMs = SystemClock.elapsedRealtime()

        removeOverlay(trackLine)

        trackLine = Polyline().apply {
            outlinePaint.color = Color.parseColor("#1565C0")
            outlinePaint.strokeWidth = 10f
            setPoints(trackPoints)
        }

        mapView.overlays.add(trackLine)

        currentPoint?.let { point ->
            trackPoints.add(point)
            trackLine?.setPoints(trackPoints)
        }

        updateTrackStats()
        updateStatus("Запись трека началась")
        Toast.makeText(this, "Запись трека началась", Toast.LENGTH_SHORT).show()
        mapView.invalidate()
    }

    private fun stopTrack() {
        isTracking = false
        updateStatus("Запись трека остановлена")
        Toast.makeText(this, "Запись трека остановлена", Toast.LENGTH_SHORT).show()
    }

    private fun addPointToTrack(point: GeoPoint) {
        if (trackPoints.isNotEmpty()) {
            val lastPoint = trackPoints.last()
            val distance = distanceBetween(lastPoint, point)

            if (distance < 1.5f) {
                return
            }

            trackDistanceMeters += distance
        }

        trackPoints.add(point)
        trackLine?.setPoints(trackPoints)

        updateTrackStats()
        mapView.invalidate()
    }

    private fun updateTrackStats() {
        val elapsedSeconds = if (trackStartTimeMs == 0L) {
            0.0
        } else {
            ((SystemClock.elapsedRealtime() - trackStartTimeMs) / 1000.0).coerceAtLeast(1.0)
        }

        val speedKmh = if (elapsedSeconds > 0) {
            (trackDistanceMeters / elapsedSeconds) * 3.6
        } else {
            0.0
        }

        tvDistance.text = String.format(
            Locale.getDefault(),
            "%.2f км",
            trackDistanceMeters / 1000.0
        )

        tvSpeed.text = String.format(
            Locale.getDefault(),
            "%.1f км/ч",
            speedKmh
        )

        tvPoints.text = String.format(
            Locale.getDefault(),
            "%d точек",
            trackPoints.size
        )
    }

    private fun saveRemindersToStorage() {
        val array = JSONArray()

        for (reminder in reminders) {
            val obj = JSONObject()
            obj.put("id", reminder.id)
            obj.put("title", reminder.title)
            obj.put("message", reminder.message)
            obj.put("radiusMeters", reminder.radiusMeters)
            obj.put("latitude", reminder.point.latitude)
            obj.put("longitude", reminder.point.longitude)
            obj.put("triggered", reminder.triggered)
            array.put(obj)
        }

        getSharedPreferences(PREFS_NAME, MODE_PRIVATE)
            .edit()
            .putString(KEY_REMINDERS, array.toString())
            .putInt(KEY_NEXT_ID, nextReminderId)
            .apply()
    }

    private fun loadRemindersFromStorage() {
        val prefs = getSharedPreferences(PREFS_NAME, MODE_PRIVATE)
        val json = prefs.getString(KEY_REMINDERS, null) ?: return

        nextReminderId = prefs.getInt(KEY_NEXT_ID, 1)

        try {
            val array = JSONArray(json)

            for (i in 0 until array.length()) {
                val obj = array.getJSONObject(i)

                val id = obj.getInt("id")
                val title = obj.getString("title")
                val message = obj.getString("message")
                val radius = obj.getDouble("radiusMeters")
                val latitude = obj.getDouble("latitude")
                val longitude = obj.getDouble("longitude")
                val triggered = obj.optBoolean("triggered", false)

                addReminder(
                    point = GeoPoint(latitude, longitude),
                    title = title,
                    message = message,
                    radiusMeters = radius,
                    triggered = triggered,
                    idFromStorage = id,
                    saveAfterCreate = false
                )
            }

            selectedReminder = reminders.lastOrNull()
            updateSelectedReminderText()

            if (reminders.isNotEmpty()) {
                updateStatus("Загружено сохранённых меток: ${reminders.size}")
            }
        } catch (e: Exception) {
            getSharedPreferences(PREFS_NAME, MODE_PRIVATE)
                .edit()
                .remove(KEY_REMINDERS)
                .apply()

            updateStatus("Сохранённые метки повреждены и были сброшены")
        }
    }

    private fun removeOverlay(overlay: Overlay?) {
        if (overlay != null) {
            mapView.overlays.remove(overlay)
        }
    }

    private fun distanceBetween(first: GeoPoint, second: GeoPoint): Float {
        val result = FloatArray(1)

        Location.distanceBetween(
            first.latitude,
            first.longitude,
            second.latitude,
            second.longitude,
            result
        )

        return result[0]
    }

    private fun formatDistance(distanceMeters: Double): String {
        return if (distanceMeters >= 1000.0) {
            String.format(Locale.getDefault(), "%.2f км", distanceMeters / 1000.0)
        } else {
            String.format(Locale.getDefault(), "%.0f м", distanceMeters)
        }
    }

    private fun updateStatus(message: String) {
        tvStatus.text = message
    }

    private fun hideKeyboard() {
        val view = currentFocus ?: View(this)
        val imm = getSystemService(Context.INPUT_METHOD_SERVICE) as InputMethodManager
        imm.hideSoftInputFromWindow(view.windowToken, 0)
    }

    private fun createNotificationChannel() {
        if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.O) {
            val channel = NotificationChannel(
                CHANNEL_ID,
                "Гео-напоминания",
                NotificationManager.IMPORTANCE_HIGH
            ).apply {
                description = "Уведомления при входе в заданную геозону"
            }

            val notificationManager =
                getSystemService(Context.NOTIFICATION_SERVICE) as NotificationManager

            notificationManager.createNotificationChannel(channel)
        }
    }

    @SuppressLint("MissingPermission")
    private fun showReminderNotification(reminder: GeoReminder) {
        if (!hasNotificationPermission()) {
            Toast.makeText(
                this,
                "Напоминание сработало, но уведомления не разрешены",
                Toast.LENGTH_LONG
            ).show()
            return
        }

        val intent = Intent(this, MainActivity::class.java).apply {
            flags = Intent.FLAG_ACTIVITY_CLEAR_TOP or Intent.FLAG_ACTIVITY_SINGLE_TOP
        }

        val pendingIntent = PendingIntent.getActivity(
            this,
            reminder.id,
            intent,
            PendingIntent.FLAG_UPDATE_CURRENT or PendingIntent.FLAG_IMMUTABLE
        )

        val notification = NotificationCompat.Builder(this, CHANNEL_ID)
            .setSmallIcon(android.R.drawable.ic_dialog_map)
            .setContentTitle(reminder.title)
            .setContentText(reminder.message)
            .setStyle(
                NotificationCompat.BigTextStyle()
                    .bigText(reminder.message)
            )
            .setPriority(NotificationCompat.PRIORITY_HIGH)
            .setAutoCancel(true)
            .setContentIntent(pendingIntent)
            .build()

        NotificationManagerCompat.from(this)
            .notify(BASE_NOTIFICATION_ID + reminder.id, notification)
    }

    private fun vibrateOnce() {
        val vibrator: Vibrator = if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.S) {
            val manager = getSystemService(Context.VIBRATOR_MANAGER_SERVICE) as VibratorManager
            manager.defaultVibrator
        } else {
            @Suppress("DEPRECATION")
            getSystemService(Context.VIBRATOR_SERVICE) as Vibrator
        }

        if (!vibrator.hasVibrator()) {
            return
        }

        if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.O) {
            vibrator.vibrate(
                VibrationEffect.createOneShot(
                    700,
                    VibrationEffect.DEFAULT_AMPLITUDE
                )
            )
        } else {
            @Suppress("DEPRECATION")
            vibrator.vibrate(700)
        }
    }
}